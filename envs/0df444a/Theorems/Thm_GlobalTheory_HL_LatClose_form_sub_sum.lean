-- Prove2me | Theorems.Thm_GlobalTheory_HL_LatClose_form_sub_sum
-- name    : GlobalTheory.HL.LatClose.form_sub_sum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:22:48.377182+00:00
-- url     : https://prove2.me/theorems/47fd22b1-6d03-4915-9fba-7b668f80f1c9
-- title:
--   Lat Close: form sub sum
-- statement:
--   The Lat Close construction uses the form sub sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CloseOnCompletedLatticeOfCloseOnFrames.lean#L31-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CloseOnCompletedLatticeOfCloseOnFrames.lean#L31-L42

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CloseOnCompletedLatticeOfCloseOnFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LatClose

theorem GlobalTheory.HL.LatClose.form_sub_sum {E : Type} [Field E] {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type} [Fintype ι] (x : Fin n → E) (a : ι → E)
    (v : ι → Fin n → E) (s : Fin n → E) :
    ∑ i, ∑ j, (x - ∑ k, a k • v k) i * Hm i j * s j =
      (∑ i, ∑ j, x i * Hm i j * s j) - ∑ k, a k * ∑ i, ∑ j, v k i * Hm i j * s j := by sorry
