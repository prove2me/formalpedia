-- Prove2me | Theorems.Thm_MoreauChance_Consistency_theorem_3_1_a
-- name    : MoreauChance.Consistency.theorem_3_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:21.882384+00:00
-- url     : https://prove2.me/theorems/5dae4af1-de7d-41c2-8815-d2e6f30467db
-- title:
--   Theorem 3.1 a), p. 9 — ϕλ is monotone in λ and inf_{λ>0} ϕλ = ϕ
-- statement:
--   Let $\mathcal H$ be a separable Hilbert space, $\mathcal Y$ a Banach space, $\xi:\Omega\to\mathbb R^m$ a random vector whose law has a density with respect to Lebesgue measure, and let $\mathcal K$ (a nonempty closed convex cone), $\mathcal C$, $h$ satisfy the conic setting (9)–(10) with $\Phi:\mathcal H\times\mathbb R^m\to\mathcal Y$ continuous. Let $\varphi$ be the probability function (1) and $\varphi_\lambda$ its inner regularization (13). Then for every $x\in\mathcal H$:
--
--   1. $\varphi_{\lambda_1}(x)\ge\varphi_{\lambda_2}(x)$ whenever $\lambda_1>\lambda_2>0$;
--   2. $$\inf_{\lambda>0}\varphi_\lambda(x)=\varphi(x).$$
--
--   So $\varphi_\lambda$ approximates $\varphi$ from above, monotonically. In particular $M(p)\subseteq M_\lambda(p)$ for every $\lambda>0$, which Proposition 5.1 and Theorem 5.4 use.
--
--   **Formalization Note** Probabilities take values in $[0,\infty]$; the infimum is over $\lambda>0$. Closedness of $\mathcal K$ is part of the conic-setting bundle (an addition, see Proposition 2.6).
-- source:
--   van Ackooij, Pérez-Aros, Soto & Vilches, Inner Moreau envelope of nonsmooth conic chance constrained optimization problems, arXiv:2301.09803v1, p. 9, Theorem 3.1 a)

import Mathlib
import Definitions.Def_MoreauChance_Consistency_Basic
import Definitions.Def_MoreauChance_Consistency_Setting

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace MoreauChance.Consistency

theorem theorem_3_1_a
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (hdens : Measure.map ξ μ ≪ volume)
    (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ) (Φ : H → EuclideanSpace ℝ (Fin m) → Y)
    (hset : IsConicSetting K C h Φ)
    (hΦ : Continuous (fun q : H × EuclideanSpace ℝ (Fin m) => Φ q.1 q.2)) (x : H) :
    (∀ l1 l2 : ℝ, 0 < l2 → l2 < l1 → probFunReg C h Φ μ ξ l2 x ≤ probFunReg C h Φ μ ξ l1 x) ∧
      (⨅ (l : ℝ) (_ : 0 < l), probFunReg C h Φ μ ξ l x) = probFun K Φ μ ξ x := by sorry

end MoreauChance.Consistency
