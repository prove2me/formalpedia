-- Prove2me | Theorems.Thm_GlobalTheory_laurent_coeff_neg_eq_zero_of_bounded
-- name    : GlobalTheory.laurent_coeff_neg_eq_zero_of_bounded
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:54:12.116864+00:00
-- url     : https://prove2.me/theorems/25887a8a-1494-439e-97df-3064449d3519
-- title:
--   Global Theory: laurent coeff neg eq zero of bounded
-- statement:
--   The Global Theory construction uses the laurent coeff neg eq zero of bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LaurentCoeffNegEqZeroOfBounded.lean#L13-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LaurentCoeffNegEqZeroOfBounded.lean#L13-L94

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LaurentCoeffNegEqZeroOfBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries
open GlobalTheory

theorem GlobalTheory.laurent_coeff_neg_eq_zero_of_bounded : ∀ (F : ℂ⸨X⸩) (T C : ℝ),
    (∀ w : ℂ, T < w.im → ∃ x : ℂ, HasSum (fun m : ℤ => F.coeff m * eTwoPi w ^ m) x ∧ ‖x‖ ≤ C) →
    ∀ m : ℤ, m < 0 → F.coeff m = 0 := by sorry
