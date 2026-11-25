-- Prove2me | Theorems.Thm_GlobalTheory_NL_Model_exists_pt
-- name    : GlobalTheory.NL.Model.exists_pt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:15:13.508138+00:00
-- url     : https://prove2.me/theorems/dd4d0340-f70a-4d9e-a59f-e8383637f17f
-- title:
--   Model: exists pt
-- statement:
--   The Model construction uses the exists pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L431-L451
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L431-L451

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

theorem GlobalTheory.NL.Model.exists_pt (h : Good K s LL) (i : Let K) :
    ∃ (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1), Pt H h i ζ τ := by sorry
