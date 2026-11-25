-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvFiniteSetDominatedSumLimitV1
-- name    : Kyprianou.Ch04.bvFiniteSetDominatedSumLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:28:09.495939+00:00
-- url     : https://prove2.me/theorems/c9908332-e969-41b9-80c3-20992053d5c6
-- title:
--   Dominated convergence for finite-subset sums with varying summands
-- statement:
--   Zero the summands outside the current finite set. Every fixed index is eventually included, and the common summable majorant allows Mathlib Tannery convergence for an arbitrary filter.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; deterministic absolutely summable jump approximation.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvFiniteSetDominatedSumLimitV1
    {I : Type} (G : Finset I → I → ℝ) (g b : I → ℝ)
    (hb : Summable b) (hbn : ∀ i, 0 ≤ b i)
    (hG : ∀ S i, |G S i| ≤ b i)
    (hlim : ∀ i, Tendsto (fun S => G S i) atTop (nhds (g i))) :
    Tendsto (fun S : Finset I => ∑ i ∈ S, G S i) atTop (nhds (∑' i, g i)) := by
  sorry
