-- Prove2me | Theorems.Thm_GlobalTheory_NL_Model_unramifiedSubfield_le_cyclotomicExt
-- name    : GlobalTheory.NL.Model.unramifiedSubfield_le_cyclotomicExt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:09:11.209884+00:00
-- url     : https://prove2.me/theorems/133cc968-2b93-5ba3-b70a-a3a70a76d8ae
-- title:
--   Model: unramified Subfield le cyclotomic Ext
-- statement:
--   The Model construction uses the unramified Subfield le cyclotomic Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L410-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L410-L410

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

theorem GlobalTheory.NL.Model.unramifiedSubfield_le_cyclotomicExt (K : FinExt l) (s : ℕ) : K0 K ≤ Ks K s := by sorry
