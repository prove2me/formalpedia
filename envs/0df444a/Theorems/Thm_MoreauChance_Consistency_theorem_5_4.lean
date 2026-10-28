-- Prove2me | Theorems.Thm_MoreauChance_Consistency_theorem_5_4
-- name    : MoreauChance.Consistency.theorem_5_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:35.310367+00:00
-- url     : https://prove2.me/theorems/4cbba069-5534-4b5e-9d85-84dd50de975b
-- title:
--   Theorem 5.4, p. 21 — values and optimal solutions of the Moreau-regularized problems (Pλ) converge to those of (P)
-- statement:
--   Let $\mathcal H$ be a separable Hilbert space, $\mathcal Y$ a Banach space, $\xi:\Omega\to\mathbb R^m$ a random vector whose law has a density with respect to Lebesgue measure, and let $\mathcal K$ (a nonempty closed convex cone), $\mathcal C$, $h$ satisfy the conic setting (9)–(10) with $\Phi:\mathcal H\times\mathbb R^m\to\mathcal Y$ continuous and $h$ sequentially weakly continuous. Fix $p\in[0,1]$ and let $\psi:\mathcal H\to\mathbb R_\infty$ be proper, convex, coercive and lower semicontinuous with $M(p)\cap\operatorname{dom}\psi\ne\emptyset$. Consider
--   $$
--   (P)\ \ \min\{\psi(x):x\in M(p)\},\qquad (P_\lambda)\ \ \min\{\mathrm e_\lambda\psi(x):x\in M_\lambda(p)\},
--   $$
--   with values $v(P)$, $v(P_\lambda)$. Then:
--
--   1. $v(P)\in\mathbb R$ and $v(P_\lambda)\in\mathbb R$ for every $\lambda>0$, and $v(P_\lambda)\to v(P)$ as $\lambda\to0^+$.
--   2. Let $\lambda_k\to0^+$ and let $x_k$ be an optimal solution of $(P_{\lambda_k})$ for every $k$. If $x_k\rightharpoonup x_0$, then $x_0$ is an optimal solution of (P). If furthermore $\operatorname{dom}\psi=\mathcal H$ and $\psi^*$ is Fréchet differentiable at every point of $\operatorname{dom}\partial\psi^*$, then $x_k\to x_0$ in norm.
--
--   This is the consistency result of the paper: the doubly regularized problems, whose data are smooth, recover both the optimal value and the optimal solutions of the original nonsmooth chance-constrained problem.
--
--   **Formalization Note** Two hypotheses are added to the page. (i) $\mathcal K$ is closed, used through Proposition 2.6. (ii) Sequential weak continuity of $h$ is assumed for the whole theorem; the page states it only in item 2, but the proof of item 1 uses the weak closedness of $M(p)$ (Theorem 3.1 d), whose proof needs it) and the Mosco convergence of Proposition 5.1 b). With $\mathcal H$ finite-dimensional the hypothesis is automatic. "$\in\mathbb R$" is stated as "neither $-\infty$ nor $+\infty$". Item 2 is vacuous when some $(P_{\lambda_k})$ has no optimal solution, exactly as on the page ("let $(x_{\lambda_k})$ be any sequence of optimal solutions"). Fréchet differentiability of the extended-valued $\psi^*$ at $u$ includes finiteness of $\psi^*$ near $u$.
-- source:
--   van Ackooij, Pérez-Aros, Soto & Vilches, Inner Moreau envelope of nonsmooth conic chance constrained optimization problems, arXiv:2301.09803v1, p. 21, Theorem 5.4

import Mathlib
import Definitions.Def_MoreauChance_Consistency_Basic
import Definitions.Def_MoreauChance_Consistency_Setting

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace MoreauChance.Consistency

theorem theorem_5_4
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (hdens : Measure.map ξ μ ≪ volume)
    (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ) (Φ : H → EuclideanSpace ℝ (Fin m) → Y)
    (hset : IsConicSetting K C h Φ)
    (hΦ : Continuous (fun q : H × EuclideanSpace ℝ (Fin m) => Φ q.1 q.2))
    (h_weak : SeqWeakCont h)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (ψ : H → EReal) (hψ : IsGammaZero ψ) (hψ_coercive : IsCoercive ψ)
    (hfeas : (feasSet K Φ μ ξ p ∩ {x | ψ x ≠ ⊤}).Nonempty) :
    (valP ψ K Φ μ ξ p ≠ ⊥ ∧ valP ψ K Φ μ ξ p ≠ ⊤ ∧
        (∀ lam : ℝ, 0 < lam →
          valPReg ψ C h Φ μ ξ lam p ≠ ⊥ ∧ valPReg ψ C h Φ μ ξ lam p ≠ ⊤) ∧
        Tendsto (fun lam => valPReg ψ C h Φ μ ξ lam p) (𝓝[>] 0) (𝓝 (valP ψ K Φ μ ξ p))) ∧
      (∀ (lamk : ℕ → ℝ) (xk : ℕ → H) (x0 : H), (∀ k, 0 < lamk k) →
        Tendsto lamk atTop (𝓝 0) →
        (∀ k, IsOptimalPReg ψ C h Φ μ ξ (lamk k) p (xk k)) → WeakConv xk x0 →
        IsOptimalP ψ K Φ μ ξ p x0 ∧
          ((∀ x, ψ x ≠ ⊤) →
            (∀ u, (subdiff (conj ψ) u).Nonempty → FrechetDiffAtE (conj ψ) u) →
            Tendsto xk atTop (𝓝 x0))) := by sorry

end MoreauChance.Consistency
