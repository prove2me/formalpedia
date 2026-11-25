-- Prove2me | Theorems.Thm_GlobalTheory_NL_Model_ex_smul
-- name    : GlobalTheory.NL.Model.ex_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:30:48.622308+00:00
-- url     : https://prove2.me/theorems/853032db-d836-40b5-be2c-e40de7af79cf
-- title:
--   Model: ex smul
-- statement:
--   The Model construction uses the ex smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L395-L400
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L395-L400

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
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} {F : LocFon l P AI H}
  {K : FinExt l} {s : ℕ} {LL : FinExt l}
open TensorProduct
variable {l : ℕ} [Fact l.Prime] {P : _root_.Formalism.BasicNotions.LocPrime l} {AI : _root_.Formalism.BasicNotions.LocAinf l P} {H : _root_.Formalism.BasicNotions.LocHW l P}
  {F : _root_.Formalism.BasicNotions.LocFon l P AI H} {K : _root_.Formalism.BasicNotions.Loc.FinExt l} {s : ℕ} {LL : _root_.Formalism.BasicNotions.Loc.FinExt l}

theorem GlobalTheory.NL.Model.ex_smul (C : _root_.Formalism.BasicNotions.LocCmpT l P AI H F) (h : _root_.Formalism.BasicNotions.Loc.Good K s LL)
    (T : _root_.GlobalTheory.NL.Lt K LL) (i : _root_.GlobalTheory.NL.Let K) (ζ : ↥LL.1) (a : _root_.GlobalTheory.NL.AA K LL)
    (x : ↥((H.W K s LL h).N T)) :
    _root_.GlobalTheory.NL.ex C h T i ζ (a • x) =
      _root_.GlobalTheory.NL.conv ((H.W K s LL h).lev i ζ a) (_root_.GlobalTheory.NL.ex C h T i ζ x) := by sorry
