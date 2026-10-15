-- Prove2me | Theorems.Thm_GenNewtonSubgrad_Composite_theorem_7_8
-- name    : GenNewtonSubgrad.Composite.theorem_7_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:46.553788+00:00
-- url     : https://prove2.me/theorems/1d4d29ab-887a-4504-8f35-14d9d9398e2b
-- title:
--   Theorem 7.8 — local Q-superlinear convergence of the composite Newton Algorithm 7.6
-- statement:
--   Consider the quadratic composite problem (7.7),
--   $$\text{minimize}\quad \varphi(x)=\tfrac12\langle Ax,x\rangle+\langle b,x\rangle+\alpha+g(x),\qquad x\in\mathbb R^n,$$
--   where $A$ is a symmetric $n\times n$ matrix, $b\in\mathbb R^n$, $\alpha\in\mathbb R$, and the regularizer $g:\mathbb R^n\to(-\infty,+\infty]$ is proper and prox-bounded. Let $\bar x$ be a stationary point, $0\in\partial\varphi(\bar x)$, at which $g$ is continuously prox-regular for $-A\bar x-b$ with modulus $r>0$, and assume the standing assumptions (H1)–(H3) for $\partial\varphi$ at $(\bar x,0)$:
--
--   1. (H1) near $(\bar x,0)$, every $(x,v)\in\operatorname{gph}\partial\varphi$ admits a direction $d$ with $-v\in\partial^2\varphi(x,v)(d)$;
--   2. (H2) $\partial\varphi$ is metrically regular around $(\bar x,0)$;
--   3. (H3) $\partial\varphi$ is semismooth\* at $(\bar x,0)$.
--
--   Then there is $\gamma_0\in(0,r^{-1}]$ such that for every $\gamma\in(0,\gamma_0)$ with $I-\gamma A$ nonsingular there is a neighbourhood $U$ of $\bar x$ such that Algorithm 7.6 with parameter $\gamma$ is well-defined from every starting point $x^0\in U$, and every sequence $\{x^k\}$ it generates from $x^0\in U$ converges Q-superlinearly to $\bar x$.
--
--   This is the paper's main result for composite optimization: a Newton-type method that needs only the proximal mapping and the second-order subdifferential of the nonconvex regularizer $g$ converges locally superlinearly under metric regularity, without convexity of $g$ and without strong metric regularity.
--
--   **Formalization Note** **Correction.** As printed, the theorem lets $\gamma$ be any value in $(0,r^{-1})$ with $I-\gamma A$ nonsingular (Step 0 of Algorithm 7.6). That fails: with $A=0$, $b=0$, $\alpha=0$ and $g(y)=\tfrac12y^2$ on $[-5,5]$, $g(y)=-1000-|y-10|$ on $[9,11]$, $g=+\infty$ elsewhere ($\bar x=0$, $r=1$, $\gamma=\tfrac12$), $\operatorname{Prox}_{\gamma g}(u)=\{9\}$ near $0$, and every run from $x^0\neq0$ near $0$ jumps to the stationary point $9$ and stays there. The proof rests on Poliquin–Rockafellar's result for $\gamma$ sufficiently small, so the theorem is posed as $\exists\gamma_0\in(0,r^{-1}]$, $\forall\gamma\in(0,\gamma_0)$, $\exists U$; the neighbourhood $U$ may depend on $\gamma$. The nonsingularity of $I-\gamma A$ (automatic for small $\gamma$) is kept as in Step 0. Runs select any point of the proximal set and any direction solving (7.18); "well-defined" means every partial run from $U$ can be continued; the stop rule of Step 1 is a constant tail. Q-superlinear convergence is in $\varepsilon$-form. Stationarity $0\in\partial\varphi(\bar x)$ is stated separately although (H1)–(H3) include it. A symmetric matrix is a self-adjoint operator on $\mathbb R^n$. $\partial$ is the analytic limiting subdifferential, which agrees with the paper's (2.9) since $\varphi$ is lower semicontinuous near $\bar x$.
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 36, Theorem 7.8 (corrected parameter range; see Formalization Note)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_Composite_Envelope
import Definitions.Def_GenNewtonSubgrad_Composite_Alg76

open Filter Topology
open scoped InnerProductSpace

namespace GenNewtonSubgrad.Composite

/-- Theorem 7.8 (p. 36), corrected parameter range: for `φ = ½⟨Ax, x⟩ + ⟨b, x⟩ + α + g` with `A`
symmetric and `g` proper, GenNewtonSubgrad.ProxReg.prox-bounded and continuously GenNewtonSubgrad.ProxReg.prox-regular at the stationary point `x̄`
for `−Ax̄ − b`, under (GenNewtonSubgrad.ProxReg.H1)–(H3) on `∂φ` at `(x̄, 0)`, there is `γ₀ ∈ (0, r⁻¹]` such that for every
`γ ∈ (0, γ₀)` with `I − γA` nonsingular, Algorithm 7.6 is well-defined from a neighbourhood `U`
of `x̄` and every run started in `U` converges Q-superlinearly to `x̄`. -/
theorem theorem_7_8 {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (α : ℝ) (g : EuclideanSpace ℝ (Fin n) → EReal)
    (xbar : EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hg : GenNewtonSubgrad.ProxReg.IsProperFn g) (hpb : GenNewtonSubgrad.ProxReg.IsProxBounded g)
    (hpr : GenNewtonSubgrad.ProxReg.IsContProxRegularAt g xbar (-(A xbar + b)) r ε)
    (hstat : 0 ∈ NonconvexSplitting.Shared.LimitingSubdiff (sumFn (quadF A b α) g) xbar)
    (hH : GenNewtonSubgrad.ProxReg.StandingH (NonconvexSplitting.Shared.LimitingSubdiff (sumFn (quadF A b α) g)) xbar 0) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ r⁻¹ ∧ ∀ γ : ℝ, 0 < γ → γ < γ₀ →
      Function.Bijective (shiftOp A γ) →
      ∃ U ∈ 𝓝 xbar, Alg76WellDefinedOn A b α g γ U ∧
        ∀ x : ℕ → EuclideanSpace ℝ (Fin n), IsAlg76Run A b α g γ x → x 0 ∈ U →
          GenNewtonSubgrad.ProxReg.IsQSuperlinear x xbar := by sorry

end GenNewtonSubgrad.Composite
