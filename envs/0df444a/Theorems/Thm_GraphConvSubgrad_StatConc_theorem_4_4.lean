-- Prove2me | Theorems.Thm_GraphConvSubgrad_StatConc_theorem_4_4
-- name    : GraphConvSubgrad.StatConc.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:20.590314+00:00
-- url     : https://prove2.me/theorems/d003fcb7-6c2c-4293-bfee-8040e7a24752
-- title:
--   Theorem 4.4, p. 15 — uniform concentration of the empirical Bregman proximal points and envelope gradients
-- statement:
--   Assume (A1)–(A3) for $\Phi$, $r$, $f$, $L$ with constants $\rho,\alpha,\sigma$, and let $\varphi=\mathbb E f(\cdot,z)+r$ and $\varphi_S=\frac1m\sum_i f(\cdot,z_i)+r$ for an i.i.d. sample $S=(z_1,\dots,z_m)\sim P^m$, $m\ge1$. Let $C\subseteq\operatorname{int}(\operatorname{dom}\Phi)$ be any set, $\delta>0$, $s\ge0$, and let $\mathcal N(C,\Phi,\delta)$ be the covering number of $C$ at scale $\delta$ in the metric $(x,y)\mapsto\|\nabla\Phi(x)-\nabla\Phi(y)\|_*$. Write $\psi_{\varepsilon L}(\lambda)=\log\mathbb E\cosh(\lambda L(z))$ and $\psi^\star_{\varepsilon L}(t)=\sup_\lambda\{t\lambda-\psi_{\varepsilon L}(\lambda)\}$.
--
--   1. For every $\bar\rho>\max(\rho,0)$, with probability at least $1-\mathcal N(C,\Phi,\delta)\exp\big(-m\,\psi^\star_{\varepsilon L}(s/\sqrt m)\big)$,
--   $$\sup_{y\in C}\big\|\operatorname{prox}^\Phi_{\varphi_S/\bar\rho}(y)-\operatorname{prox}^\Phi_{\varphi/\bar\rho}(y)\big\|\le\sqrt{\frac{4(\sigma+s)^2}{\alpha(\bar\rho-\rho)^2m}}+\frac{2\bar\rho\delta}{\alpha(\bar\rho-\rho)}.$$
--   2. If in addition $\rho>0$, $\Phi$ is twice differentiable on $\operatorname{int}(\operatorname{dom}\Phi)$ and $\nabla^2\Phi(y)$ is invertible for $y\in C$, then with the same probability
--   $$\sup_{y\in C}\big\|\nabla(\varphi_S)^\Phi_{1/2\rho}(y)-\nabla\varphi^\Phi_{1/2\rho}(y)\big\|^*_y\le\sqrt{\frac{16(\sigma+s)^2}{\alpha m}}+\frac{8\rho\delta}{\alpha}.$$
--
--   This is the paper's main result: a uniform, high-probability bound on the distance between the proximal points (equivalently, by Theorem 3.1, the envelope gradients) of the empirical and the population risks. Through the correspondence between proximal points and subgradients it yields the closeness of the subdifferential graphs of $\varphi_S$ and $\varphi$, so that approximately stationary points of the empirical problem are approximately stationary for the population problem. The bound holds uniformly over $y\in C$, not only pointwise, and for a general Legendre $\Phi$, not only for $\Phi=\frac12\|\cdot\|_2^2$.
--
--   **Formalization Note** "With probability $1-p$, the bound holds" is stated as: the outer measure of the set of samples for which some $y\in C$ violates the bound is at most $p$. The covering number is replaced by the size $|T|$ of an arbitrary finite $\delta$-net $T$ of $C$ (closed $\delta$-balls, centres in $\operatorname{int}(\operatorname{dom}\Phi)$), fixed before the sample; the covering number is the least such size. Since $\psi^\star$ may be $+\infty$, $\exp(-m\psi^\star_{\varepsilon L}(s/\sqrt m))$ is replaced by $\exp(-m(\lambda s/\sqrt m-\psi_{\varepsilon L}(\lambda)))$ for an arbitrary $\lambda$ with $\cosh(\lambda L)$ integrable, which is equivalent. Proximal maps are sets; the first event asks for some point of each proximal set at distance above the bound. The second display is the case $\bar\rho=2\rho$ (envelope parameter $1/(2\rho)$), which needs $\rho>0$; its $\|\cdot\|^*_x$ on the page is read as the local dual norm at $y$, defined through $\nabla^2\Phi(y)^{-1}$, so invertibility of the Hessian on $C$ is assumed. Added: $\bar\rho>0$, together with the additions recorded in the definitions file (proper convex $\operatorname{dom} r$, measurable integrable loss, closedness of $f(\cdot,z)+r$ and of $\varphi$, $\varphi$ bounded below).
-- source:
--   Davis, Drusvyatskiy, Graphical Convergence of Subgradients in Nonconvex Optimization and Learning, arXiv:1810.07590v2, p. 15, Theorem 4.4 (proof pp. 15–16)

import Mathlib
import Definitions.Def_GraphConvSubgrad_StatConc_Setting

namespace GraphConvSubgrad.StatConc

open MeasureTheory

/-- Theorem 4.4 (Concentration of the stationarity measure), p. 15. Under (A1)–(A3), for every
`C ⊆ int (dom Φ)`, `δ > 0`, `s ≥ 0`, sample size `m ≥ 1`, every finite `δ`-net `T` of `C` in the
metric `‖∇Φ(x) − ∇Φ(y)‖_*` (centres in `int (dom Φ)`), and every `λ` with `cosh(λ L)` integrable:
(1) for `0 < ρ̄`, `ρ < ρ̄`, the probability that some `y ∈ C` has
`‖prox^Φ_{φ_S/ρ̄}(y) − prox^Φ_{φ/ρ̄}(y)‖ > √(4(σ+s)²/(α(ρ̄−ρ)²m)) + 2ρ̄δ/(α(ρ̄−ρ))` is at most
`|T| exp(−m(λ s/√m − ψ_{εL}(λ)))`;
(2) if moreover `ρ > 0`, `Φ` is twice differentiable on `int (dom Φ)` and `∇²Φ(y)` is invertible
for `y ∈ C`, the probability that some `y ∈ C` has
`‖∇(φ_S)^Φ_{1/2ρ}(y) − ∇φ^Φ_{1/2ρ}(y)‖*_y > √(16(σ+s)²/(αm)) + 8ρδ/α` obeys the same bound. -/
theorem theorem_4_4 {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Φ r : ExtFn E) (f : E → Ω → ℝ) (L : Ω → ℝ) (ρ α σ : ℝ)
    (hA : Assumptions P Φ r f L ρ α σ)
    (C : Set E) (hC : C ⊆ interior Φ.dom) (δ s : ℝ) (hδ : 0 < δ) (hs : 0 ≤ s)
    (m : ℕ) (hm : 0 < m)
    (T : Finset E) (hT : (T : Set E) ⊆ interior Φ.dom)
    (hnet : ∀ y ∈ C, ∃ t ∈ T, ‖fderiv ℝ Φ.val y - fderiv ℝ Φ.val t‖ ≤ δ)
    (lam : ℝ) (hlam : Integrable (fun z => Real.cosh (lam * L z)) P) :
    (∀ rhoBar : ℝ, 0 < rhoBar → ρ < rhoBar →
      (Measure.pi fun _ : Fin m => P)
          {S | ∃ y ∈ C, ∃ a ∈ proxSet Φ (empRisk r f S) rhoBar y,
            ∃ b ∈ proxSet Φ (popRisk P r f) rhoBar y,
              Real.sqrt (4 * (σ + s) ^ 2 / (α * (rhoBar - ρ) ^ 2 * m))
                + 2 * rhoBar * δ / (α * (rhoBar - ρ)) < ‖a - b‖}
        ≤ (T.card : ENNReal) *
            ENNReal.ofReal (Real.exp (-((m : ℝ) * (lam * (s / Real.sqrt m) - logMGFSym P L lam))))) ∧
    (0 < ρ → DifferentiableOn ℝ (fderiv ℝ Φ.val) (interior Φ.dom) →
      (∀ y ∈ C, HessInvertible Φ y) →
      (Measure.pi fun _ : Fin m => P)
          {S | ∃ y ∈ C, Real.sqrt (16 * (σ + s) ^ 2 / (α * m)) + 8 * ρ * δ / α <
            localDualNorm Φ y (fderiv ℝ (envelope Φ (empRisk r f S) (2 * ρ)) y
              - fderiv ℝ (envelope Φ (popRisk P r f) (2 * ρ)) y)}
        ≤ (T.card : ENNReal) *
            ENNReal.ofReal (Real.exp (-((m : ℝ) * (lam * (s / Real.sqrt m) - logMGFSym P L lam))))) := by sorry

end GraphConvSubgrad.StatConc
