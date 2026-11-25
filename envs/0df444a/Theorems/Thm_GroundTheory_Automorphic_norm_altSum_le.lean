-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_norm_altSum_le
-- name    : GroundTheory.Automorphic.norm_altSum_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:35:34.531252+00:00
-- url     : https://prove2.me/theorems/5a2ece06-bb09-48bd-a79c-cd66b21c1c2d
-- title:
--   Automorphic: norm alt Sum le
-- statement:
--   The Automorphic construction uses the norm alt Sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalDiscreteness/MixedDifference.lean#L28-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalDiscreteness/MixedDifference.lean#L28-L39

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

theorem GroundTheory.Automorphic.norm_altSum_le : ∀ (k : ℕ) {ρ : E → F}, ContDiff ℝ k ρ → ∀ {B : ℝ},
    (∀ w, ‖iteratedFDeriv ℝ k ρ w‖ ≤ B) → ∀ (v : Fin k → E) (z : E),
      ‖altSum k ρ v z‖ ≤ B * ∏ i, ‖v i‖
  := by sorry
