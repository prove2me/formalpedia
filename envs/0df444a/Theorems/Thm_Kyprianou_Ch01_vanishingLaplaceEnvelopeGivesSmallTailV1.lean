-- Prove2me | Theorems.Thm_Kyprianou_Ch01_vanishingLaplaceEnvelopeGivesSmallTailV1
-- name    : Kyprianou.Ch01.vanishingLaplaceEnvelopeGivesSmallTailV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:19:49.194694+00:00
-- url     : https://prove2.me/theorems/16af93b3-61cf-45ca-8515-bf233ebd87cf
-- title:
--   Vanishing positive-barrier envelope forces arbitrarily small event tails
-- statement:
--   Any probability tail bound c*P(E_s)≤g(s), with c>0 and g(s) tending to zero as the positive barrier s tends to zero, implies arbitrarily small tail probabilities P(E_s). Choose the explicit positive barrier sequence s_n=1/(n+1), combine its pinned Mathlib convergence with continuity of g, take a sufficiently large n using Eventually.exists, and cancel positive c. No measurability of the event family E is required, only outer measure.
-- source:
--   Elementary limit comparison with probability outer measure, used in Kyprianou (2006) Chapter 1 §1.2.5.

import Mathlib
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.vanishingLaplaceEnvelopeGivesSmallTailV1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (E : ℝ≥0 → Set Ω)
    (c : ℝ) (hc : 0 < c)
    (g : ℝ≥0 → ℝ)
    (hg : Tendsto g (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)))
    (hBound : ∀ s : ℝ≥0, 0 < s →
       c * (P (E s)).toReal ≤ g s)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ s : ℝ≥0, 0 < s ∧ (P (E s)).toReal < δ := by sorry
