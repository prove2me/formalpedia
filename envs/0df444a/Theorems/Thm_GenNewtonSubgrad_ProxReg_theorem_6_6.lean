-- Prove2me | Theorems.Thm_GenNewtonSubgrad_ProxReg_theorem_6_6
-- name    : GenNewtonSubgrad.ProxReg.theorem_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:36:50.870872+00:00
-- url     : https://prove2.me/theorems/0071da5f-ae84-484a-9878-572e7e0be0d1
-- title:
--   Theorem 6.6, p. 28 (corrected range) — local superlinear convergence of the prox-based Newton Algorithm 6.2 for continuously prox-regular functions
-- statement:
--   Let $\varphi:\mathbb R^n\to(-\infty,\infty]$ be proper and prox-bounded, and let $\bar x$ be a solution of $0\in\partial\varphi(\bar x)$ (1.5). Assume that $\varphi$ is continuously prox-regular at $\bar x$ for $0$ with constants $r,\varepsilon>0$ in (4.1), and that the standing assumptions hold for $\partial\varphi$ at $(\bar x,0)$:
--
--   1. (H1) the second-order inclusion $-v\in\partial^2\varphi(x,v)(d)$ is solvable in $d$ for every $(x,v)\in\operatorname{gph}\partial\varphi$ near $(\bar x,0)$;
--   2. (H2) $\partial\varphi$ is metrically regular around $(\bar x,0)$;
--   3. (H3) $\partial\varphi$ is semismooth* at $(\bar x,0)$.
--
--   Then there is $\lambda_0$ with $0<\lambda_0\le r^{-1}$ such that for every parameter $\lambda\in(0,\lambda_0)$ there is a neighbourhood $U\subseteq U_\lambda=\operatorname{rge}(I+\lambda\partial\varphi)$ of $\bar x$ such that Algorithm 6.2 is well-defined from every $x^0\in U$, and every sequence $(x^k)$ it generates from $x^0\in U$ converges Q-superlinearly to $\bar x$:
--   $$x^k\to\bar x\quad\text{and}\quad\lim_{k\to\infty}\frac{\|x^{k+1}-\bar x\|}{\|x^k-\bar x\|}=0.$$
--
--   This is the main result of §6: under metric regularity (not strong metric regularity) and semismoothness*, the prox-based Newton method converges locally superlinearly for prox-regular functions.
--
--   **Correction.** As printed, the theorem allows any $\lambda\in(0,r^{-1})$ in Step 0 of Algorithm 6.2. For $\varphi(y)=\tfrac12y^2$ on $[-5,5]$, $-1000-|y-10|$ on $[9,11]$, $+\infty$ elsewhere, with $\bar x=0$, $r=1$ and $\lambda=\tfrac12$, every hypothesis holds but $\operatorname{Prox}_\lambda\varphi(x)=\{9\}$ near $0$, and the algorithm moves to the stationary point $9$ in one step and stops there. The proof relies on Lemma 6.3, i.e. on Poliquin–Rockafellar [53, Theorem 4.4], which holds for $\lambda$ sufficiently small; the theorem is stated in that form. The quantifier order is $\exists\lambda_0\in(0,r^{-1}]\ \forall\lambda\in(0,\lambda_0)\ \exists U$, so $U$ may depend on $\lambda$; $\lambda_0>0$ is part of the conclusion.
--
--   **Formalization Note.** "Converges superlinearly" is read as Q-superlinear convergence (the notion of Theorem 5.7, to which the proof reduces), in $\varepsilon$-form: for every $\varepsilon>0$, eventually $\|x^{k+1}-\bar x\|\le\varepsilon\|x^k-\bar x\|$. The conclusion holds for every run: every selection from the argmin set $\operatorname{Prox}_\lambda\varphi(x^k)$ and every direction solving (6.5). Well-definedness means every partial run from $U$ can be continued (a proximal point exists and (6.5) is solvable). $U\subseteq U_\lambda$ is required because Step 0 starts in $U_\lambda$. $\partial$ is the analytic limiting subdifferential, which agrees with the paper's (2.9) for $\varphi$ l.s.c. around $\bar x$.
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 28, Theorem 6.6 (corrected parameter range; see Formalization Note)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_ProxReg_Envelope
import Definitions.Def_GenNewtonSubgrad_ProxReg_Alg62
open Filter Topology

namespace GenNewtonSubgrad.ProxReg

theorem theorem_6_6 {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → EReal)
    (xbar : EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hproper : IsProperFn φ) (hbdd : IsProxBounded φ)
    (hreg : IsContProxRegularAt φ xbar 0 r ε)
    (hH : StandingH (NonconvexSplitting.Shared.LimitingSubdiff φ) xbar 0) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ r⁻¹ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ U ∈ 𝓝 xbar, U ⊆ rgeShift φ lam ∧ Alg62WellDefinedOn φ lam U ∧
        ∀ x : ℕ → EuclideanSpace ℝ (Fin n), IsAlg62Run φ lam x → x 0 ∈ U →
          IsQSuperlinear x xbar := by sorry

end GenNewtonSubgrad.ProxReg
