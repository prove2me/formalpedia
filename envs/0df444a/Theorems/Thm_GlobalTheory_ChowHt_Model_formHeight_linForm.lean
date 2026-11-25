-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_Model_formHeight_linForm
-- name    : GlobalTheory.ChowHt.Model.formHeight_linForm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:01:24.195939+00:00
-- url     : https://prove2.me/theorems/d8152ddf-decd-4858-b441-5f91cfc50bb6
-- title:
--   Model: form Height lin Form
-- statement:
--   The Model construction uses the form Height lin Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/BlockSphereMeanLinForm.lean#L107-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/BlockSphereMeanLinForm.lean#L107-L128

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BlockSphereMeanLinForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial NumberField
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.ChowHt.Model

theorem GlobalTheory.ChowHt.Model.formHeight_linForm {F : Type} [Field F] [NumberField F] {N n : ℕ}
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ σ, (A σ).det ≠ 0) (y : Fin N → F) (hy : y ≠ 0) :
    formHeight 1 w A (linForm y) = pointHeight w A y := by sorry
