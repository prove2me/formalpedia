-- Prove2me | Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_lemma_9_bounds
-- name    : LostSalesConstantOrder.LargeLeadTime.lemma_9_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:24.606699+00:00
-- url     : https://prove2.me/theorems/76de8aed-8f46-4494-943f-5fdb84c568df
-- title:
--   Lemma 9 (bounds): tails of $i^r_\infty$ and $\mathbb E[(I^r_\infty)^2]\le2\Theta_r^{-3}\mathbb E^2[D]$
-- statement:
--   Let $D_1,D_2,\dots$ be i.i.d. with law $\mathcal D$ (finite third moment, not deterministic), $r\in[0,\mathbb E[D])$ and $\Theta_r=(\mathbb E[D]-r)^2/(4(\mathbb E^2[D]+\mathbb E[D^2]))$. Then:
--   1. $\mathbb P(i^r_\infty\ge k)\le\Theta_r^{-1}(1-\Theta_r)^k$ for every $k\ge0$;
--   2. $\displaystyle\sum_{k=0}^\infty\sum_{j=k}^\infty\mathbb P(i^r_\infty\ge j)\le\Theta_r^{-3}$;
--   3. $\mathbb E[(I^r_\infty)^2]\le2\Theta_r^{-3}\mathbb E^2[D]$.
--
--   These are the three estimates used to bound the terms (9) and (12) in the proof of Theorem 8.
--
--   **Formalization Note** Probabilities and the second moment are in $[0,\infty]$; $I^r_\infty$ is the supremum in $[0,\infty]$, so its second moment is not a truncated value.
-- source:
--   Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, Asymptotic Optimality of Constant-Order Policies for Lost Sales Inventory Models with Large Lead Times, arXiv:1211.4063v2, p. 10, Lemma 9 (second sentence)

import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_RandomWalk

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesConstantOrder.LargeLeadTime

/-- Lemma 9, p. 10 (second part): for `r ∈ [0, E[D])`,
`P(i^r_∞ ≥ k) ≤ Θ_r⁻¹(1 − Θ_r)^k` for every `k`, `Σ_{k=0}^∞ Σ_{j=k}^∞ P(i^r_∞ ≥ j) ≤ Θ_r⁻³`, and
`E[(I^r_∞)²] ≤ 2Θ_r⁻³E²[D]`. -/
theorem lemma_9_bounds (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P)
    (r : ℝ≥0) (hr : (r : ℝ) < CappedBaseStock.mean P) :
    (∀ k : ℕ, CappedBaseStock.demandPathLaw P {d | k ≤ argmaxWalk r d} ≤
        ENNReal.ofReal ((1 - theta P r) ^ k / theta P r)) ∧
    (∑' (k : ℕ) (j : Set.Ici k),
        CappedBaseStock.demandPathLaw P {d | (j : ℕ) ≤ argmaxWalk r d} ≤
      ENNReal.ofReal (1 / theta P r ^ 3)) ∧
    ∫⁻ d, supWalk r d ^ 2 ∂CappedBaseStock.demandPathLaw P ≤
      ENNReal.ofReal (2 * CappedBaseStock.mean P ^ 2 / theta P r ^ 3) := by sorry

end LostSalesConstantOrder.LargeLeadTime
