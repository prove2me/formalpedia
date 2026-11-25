-- Prove2me | Theorems.Thm_GlobalTheory_WachFree_wach_free
-- name    : GlobalTheory.WachFree.wach_free
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:36:22.426686+00:00
-- url     : https://prove2.me/theorems/505aba60-0066-4861-9146-19d2aca5e692
-- title:
--   Wach Free: wach free
-- statement:
--   The Wach Free construction uses the wach free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemXSmulOfProjective.lean#L186-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemXSmulOfProjective.lean#L186-L231

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvrComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemXSmulOfProjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct
open GlobalTheory GlobalTheory.WachFree
set_option maxHeartbeats 1600000

theorem GlobalTheory.WachFree.wach_free {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (hT : IsCrys (P.PD K) T.ρ) :
    Nonempty (Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T))
      (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K s LL h).N T)) := by sorry
