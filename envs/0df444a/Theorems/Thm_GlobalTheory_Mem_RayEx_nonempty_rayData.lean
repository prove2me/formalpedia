-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayEx_nonempty_rayData
-- name    : GlobalTheory.Mem.RayEx.nonempty_rayData
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:45:38.994191+00:00
-- url     : https://prove2.me/theorems/60141adb-be8a-4ff5-8b1b-bf4574b92714
-- title:
--   Ray Ex: nonempty ray Data
-- statement:
--   The Ray Ex construction uses the nonempty ray Data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayDataNonempty.lean#L158-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayDataNonempty.lean#L158-L187

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayDataNonempty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayEx
open NumberField IsDedekindDomain
open Classical

theorem GlobalTheory.Mem.RayEx.nonempty_rayData (K : Type) [Field K] [NumberField K] (M : ℕ) (hM : 2 ≤ M) : Nonempty (RayData K M) := by sorry
