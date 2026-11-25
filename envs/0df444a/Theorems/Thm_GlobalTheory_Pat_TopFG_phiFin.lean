-- Prove2me | Theorems.Thm_GlobalTheory_Pat_TopFG_phiFin
-- name    : GlobalTheory.Pat.TopFG.phiFin
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:29.716866+00:00
-- url     : https://prove2.me/theorems/12fdb264-6900-4855-bd79-fade307e748b
-- title:
--   Top FG: phi Fin
-- statement:
--   The Top FG construction uses the phi Fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/FiniteCocycles.lean#L147-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/FiniteCocycles.lean#L147-L172

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Polynomial IsLocalRing
noncomputable section
open IsLocalRing
open GlobalTheory GlobalTheory.Pat

theorem GlobalTheory.Pat.TopFG.phiFin (l : ℕ) [NeZero l] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (h : TopFG G) : PhiFin l G := by sorry
