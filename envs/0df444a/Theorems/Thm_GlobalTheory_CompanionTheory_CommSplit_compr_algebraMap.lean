-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CommSplit_compr_algebraMap
-- name    : GlobalTheory.CompanionTheory.CommSplit.compr_algebraMap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:32:54.402001+00:00
-- url     : https://prove2.me/theorems/61cf84ea-49c7-4574-82b3-aed7d64182cc
-- title:
--   Comm Split: compr algebra Map
-- statement:
--   The Comm Split construction uses the compr algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankAdjoinLeAdd.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankAdjoinLeAdd.lean#L33-L40

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankAdjoinLeAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CommSplit
open Module
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.CommSplit.compr_algebraMap (W W' : Submodule ℂ V) (hc : IsCompl W W') (t : ℂ) :
    compr W W' hc (algebraMap ℂ (End ℂ V) t) = algebraMap ℂ (End ℂ W) t := by sorry
