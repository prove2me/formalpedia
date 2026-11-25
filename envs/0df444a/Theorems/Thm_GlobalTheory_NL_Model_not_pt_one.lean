-- Prove2me | Theorems.Thm_GlobalTheory_NL_Model_not_pt_one
-- name    : GlobalTheory.NL.Model.not_pt_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:15:37.564245+00:00
-- url     : https://prove2.me/theorems/c9090d81-f09b-4972-9ab2-08326d13a55b
-- title:
--   Model: not pt one
-- statement:
--   The Model construction uses the not pt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L453-L464
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L453-L464

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

theorem GlobalTheory.NL.Model.not_pt_one (h : Good K s LL) (i : Let K) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) : ¬ Pt H h i 1 τ := by sorry
