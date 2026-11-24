-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_Model_linSubst_linForm
-- name    : GlobalTheory.ChowHt.Model.linSubst_linForm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:09:57.598729+00:00
-- url     : https://prove2.me/theorems/ced05792-c4bb-4876-a5fe-415330c4e08a
-- title:
--   Model: lin Subst lin Form
-- statement:
--   The Model construction uses the lin Subst lin Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/BlockSphereMeanLinForm.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/BlockSphereMeanLinForm.lean#L42-L47

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

theorem GlobalTheory.ChowHt.Model.linSubst_linForm {R : Type} [CommRing R] {N n : ℕ} (M : Matrix (Fin N) (Fin n) R)
    (c : Fin N → R) : linSubst M (linForm c) = linForm (fun k => ∑ j, M j k * c j) := by sorry
