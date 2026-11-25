-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_Model_isChowForm_line
-- name    : GlobalTheory.ChowHt.Model.isChowForm_line
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:59:22.045994+00:00
-- url     : https://prove2.me/theorems/b885372e-7916-5aca-b496-739782d594fa
-- title:
--   Model: is Chow Form line
-- statement:
--   The Model construction uses the is Chow Form line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/BlockSphereMeanLinForm.lean#L130-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/BlockSphereMeanLinForm.lean#L130-L164

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

theorem GlobalTheory.ChowHt.Model.isChowForm_line (k : Type) [Field k] :
    IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) k)) 1 1
      (Matrix.of fun i j : Fin 2 => (X (i, j) : MvPolynomial (Fin 2 × Fin 2) k)).det := by sorry
