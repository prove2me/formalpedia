-- Prove2me | Theorems.Thm_GlobalTheory_DatumSign_finrank_le
-- name    : GlobalTheory.DatumSign.finrank_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:51.472523+00:00
-- url     : https://prove2.me/theorems/2899c832-b429-5525-9084-f998f4f15f2b
-- title:
--   Datum Sign: finrank le
-- statement:
--   The Datum Sign construction uses the finrank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/PEqQOfNeg.lean#L42-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/PEqQOfNeg.lean#L42-L78

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_PEqQOfNeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DatumSign
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Module
open scoped TensorProduct
variable {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem GlobalTheory.DatumSign.finrank_le (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (A J K : V →ₗ[ℝ] V) (s : ℝ) (hs : 0 < s)
    (hA : ∀ x, A (A x) = -((s * s) • x)) (hJ : ∀ x, J (J x) = -x) (hK : ∀ x, K (K x) = -x)
    (hKA : K ∘ₗ A = A ∘ₗ K) (pJ : ∀ x, x ≠ 0 → 0 < B (J x) x) (pK : ∀ x, x ≠ 0 → 0 < B (K x) x) :
    finrank ℝ (LinearMap.ker (J ∘ₗ A - s • LinearMap.id)) ≤ finrank ℝ (LinearMap.ker (K ∘ₗ A - s • LinearMap.id)) := by sorry
