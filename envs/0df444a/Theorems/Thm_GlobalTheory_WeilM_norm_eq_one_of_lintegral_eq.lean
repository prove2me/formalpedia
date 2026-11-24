-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_norm_eq_one_of_lintegral_eq
-- name    : GlobalTheory.WeilM.norm_eq_one_of_lintegral_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:19.563665+00:00
-- url     : https://prove2.me/theorems/d29fc3cd-4f9d-4655-ab2d-fe01b5a09fec
-- title:
--   Weil M: norm eq one of lintegral eq
-- statement:
--   The Weil M construction uses the norm eq one of lintegral eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L69-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L69-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R] {κ : Type} [Fintype κ] {G : Type} [Group G]

theorem GlobalTheory.WeilM.norm_eq_one_of_lintegral_eq {X : Type} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ} {a : ℂ}
    (h : ∫⁻ x, ‖(a • f) x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) (h0 : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≠ 0)
    (h1 : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≠ ⊤) : ‖a‖ = 1 := by sorry
