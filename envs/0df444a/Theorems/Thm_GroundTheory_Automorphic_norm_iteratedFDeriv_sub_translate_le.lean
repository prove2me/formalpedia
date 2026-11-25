-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_norm_iteratedFDeriv_sub_translate_le
-- name    : GroundTheory.Automorphic.norm_iteratedFDeriv_sub_translate_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:35:22.040549+00:00
-- url     : https://prove2.me/theorems/e2989401-b8a5-4503-9a3e-a2baae5cd2f5
-- title:
--   Automorphic: norm iterated FDeriv sub translate le
-- statement:
--   The Automorphic construction uses the norm iterated FDeriv sub translate le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalDiscreteness/MixedDifference.lean#L9-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalDiscreteness/MixedDifference.lean#L9-L26

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalDiscreteness_AltSum
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalDiscreteness_MixedDifference
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem GroundTheory.Automorphic.norm_iteratedFDeriv_sub_translate_le {k : ℕ} {ρ : E → F} (hρ : ContDiff ℝ (k + 1) ρ)
    {B : ℝ} (hB : ∀ w, ‖iteratedFDeriv ℝ (k + 1) ρ w‖ ≤ B) (y w : E) :
    ‖iteratedFDeriv ℝ k (fun t => ρ (t + y) - ρ t) w‖ ≤ B * ‖y‖ := by sorry
