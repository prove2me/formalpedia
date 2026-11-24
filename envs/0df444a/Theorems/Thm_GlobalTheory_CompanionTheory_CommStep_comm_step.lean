-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CommStep_comm_step
-- name    : GlobalTheory.CompanionTheory.CommStep.comm_step
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:33:25.065858+00:00
-- url     : https://prove2.me/theorems/2db2b93b-0c8b-40ad-9c3d-ca901eb6dedd
-- title:
--   Comm Step: comm step
-- statement:
--   The Comm Step construction uses the comm step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CommuteOfMemAdjoin.lean#L90-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CommuteOfMemAdjoin.lean#L90-L105

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

theorem GlobalTheory.CompanionTheory.CommStep.comm_step : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (l : ℕ)
    (a : Fin (l + 1) → Module.End ℂ V), (∀ i j, Commute (a i) (a j)) → ∀ x : ℕ,
    Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
      x * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ)) +
        Module.finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
          (LinearMap.mulRight ℂ (a 0 ^ x))) := by sorry
