-- Prove2me | Theorems.Thm_GlobalTheory_NL_Model_not_graded
-- name    : GlobalTheory.NL.Model.not_graded
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:22.937906+00:00
-- url     : https://prove2.me/theorems/64f8c05c-baa0-45b5-b603-346886d23176
-- title:
--   Model: not graded
-- statement:
--   The Model construction uses the not graded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L171-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L171-L211

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NotFullBot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnramifiedSubfieldLeCyclotomicExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NL GlobalTheory.NL.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.NL
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

theorem GlobalTheory.NL.Model.not_graded :
    ¬ Graded (latSpan (LL := L) (fun _ : Unit =>
      (((Pi.single 0 (1, 0) : ℤ → L × L) + (Pi.single (-1) (0, 1) : ℤ → L × L))))) := by sorry
