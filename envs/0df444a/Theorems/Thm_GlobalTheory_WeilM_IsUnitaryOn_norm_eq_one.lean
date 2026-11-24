-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_IsUnitaryOn_norm_eq_one
-- name    : GlobalTheory.WeilM.IsUnitaryOn.norm_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:13.879795+00:00
-- url     : https://prove2.me/theorems/1db7b79d-7822-44cf-a1de-b66da97be72e
-- title:
--   Is Unitary On: norm eq one
-- statement:
--   The Is Unitary On construction uses the norm eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L78-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L78-L85

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

theorem GlobalTheory.WeilM.IsUnitaryOn.norm_eq_one [TopologicalSpace R] {C : TestClass R} {om om' : G →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsUnitaryOn C om) (h' : IsUnitaryOn C om') {μ : @Measure (κ → R) (borel _)}
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) {φ : (κ → R) → ℂ} (hφ : φ ∈ C.sp κ)
    (h0 : ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ ≠ 0) (h1 : ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ ≠ ⊤) {g : G} {a : ℂ} (ha : om' g φ = a • om g φ) :
    ‖a‖ = 1 := by sorry
