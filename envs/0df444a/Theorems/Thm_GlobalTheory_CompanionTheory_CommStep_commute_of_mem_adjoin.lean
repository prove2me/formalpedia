-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CommStep_commute_of_mem_adjoin
-- name    : GlobalTheory.CompanionTheory.CommStep.commute_of_mem_adjoin
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:32:59.951102+00:00
-- url     : https://prove2.me/theorems/4b5732f4-2c13-4675-bcc7-58ad5c505aa0
-- title:
--   Comm Step: commute of mem adjoin
-- statement:
--   The Comm Step construction uses the commute of mem adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CommuteOfMemAdjoin.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CommuteOfMemAdjoin.lean#L7-L16

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CommuteOfMemAdjoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CommStep
open Module

theorem GlobalTheory.CompanionTheory.CommStep.commute_of_mem_adjoin {V : Type} [AddCommGroup V] [Module ℂ V] {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V) (hc : ∀ i j, Commute (a i) (a j)) (i : Fin (l + 1))
    {y : Module.End ℂ V} (hy : y ∈ Algebra.adjoin ℂ (Set.range a)) : Commute y (a i) := by sorry
