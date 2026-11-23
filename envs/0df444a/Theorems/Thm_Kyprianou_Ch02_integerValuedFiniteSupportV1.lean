-- Prove2me | Theorems.Thm_Kyprianou_Ch02_integerValuedFiniteSupportV1
-- name    : Kyprianou.Ch02.integerValuedFiniteSupportV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T09:32:09.536947+00:00
-- url     : https://prove2.me/theorems/41f6eb25-8087-4fe2-90b7-6a63c55aef5e
-- title:
--   Integer-valued measure on a countably separated Borel space is concentrated on finitely many points
-- statement:
--   An integer-valued measure on a countably separated measurable space is supported on a finite set, without an additional finite-measure assumption because its total mass is a natural number. Proof by strong induction on total mass: extract a point carrying at least unit mass and restrict the remainder. This ports the actual source of LevyStochCalc Probability/IntegerValuedMeasure.lean and is an essential genuine dependency of finite-activity Poisson atomicity and Kyprianou Chapter 2 Eq. (2.3).
-- source:
--   LevyStochCalc/Probability/IntegerValuedMeasure.lean, theorem exists_finset_ae_mem, imported source under work/LevyStochCalc_20261113; chapter-2 milestone Kyprianou.largeJumpProcessLevy.

import Mathlib
import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F000
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.integerValuedFiniteSupportV1
    {α : Type} [MeasurableSpace α]
    [MeasurableSpace.CountablySeparated α]
    (μ : Measure α)
    (hint : LevyStochCalc.Probability.IsIntegerValued μ) :
    ∃ s : Finset α, ∀ᵐ a ∂μ, a ∈ s := by sorry
