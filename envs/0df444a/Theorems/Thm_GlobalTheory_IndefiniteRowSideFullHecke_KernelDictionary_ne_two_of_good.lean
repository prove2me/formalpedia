-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_KernelDictionary_ne_two_of_good
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.KernelDictionary.ne_two_of_good
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:08:25.729199+00:00
-- url     : https://prove2.me/theorems/93df394a-8d81-4fcc-9418-600f5e5aac10
-- title:
--   Kernel Dictionary: ne two of good
-- statement:
--   The Kernel Dictionary construction uses the ne two of good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/KernelDictionary.lean#L146-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/KernelDictionary.lean#L146-L148

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MapCSmulMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_RoundDown
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_OfKillsOne
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_KernelDictionary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.KernelDictionary
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.IndefiniteRowSideFullHecke.KernelDictionary.ne_two_of_good {K LL : FinExt l} (h : Good K 1 LL) : l ≠ 2 := by sorry
