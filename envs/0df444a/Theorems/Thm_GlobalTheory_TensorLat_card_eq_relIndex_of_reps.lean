-- Prove2me | Theorems.Thm_GlobalTheory_TensorLat_card_eq_relIndex_of_reps
-- name    : GlobalTheory.TensorLat.card_eq_relIndex_of_reps
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T17:05:46.988209+00:00
-- url     : https://prove2.me/theorems/f689ad82-2d5c-5c72-88e2-aa260990b440
-- title:
--   Tensor Lat: card eq rel Index of reps
-- statement:
--   The Tensor Lat construction uses the card eq rel Index of reps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsCoeEqSpanDetOfIntVecLe.lean#L54-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsCoeEqSpanDetOfIntVecLe.lean#L54-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsIntSmulMemSpan
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_DualLattices_WedgeNeZeroOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
open scoped nonZeroDivisors

theorem GlobalTheory.TensorLat.card_eq_relIndex_of_reps {M : Type*} [AddCommGroup M] {A B : AddSubgroup M} {R : Finset M}
    (hR : ∀ y ∈ R, y ∈ B) (hR' : ∀ y ∈ B, ∃! r ∈ R, y - r ∈ A) : R.card = A.relIndex B := by sorry
