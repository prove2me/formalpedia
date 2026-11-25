-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_norm_altSum_le
-- name    : GroundTheory.Automorphic.exists_norm_altSum_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:49.800605+00:00
-- url     : https://prove2.me/theorems/a8f6ce5c-2689-4edf-8507-f9be57cfdefb
-- title:
--   Automorphic: exists norm alt Sum le
-- statement:
--   The Automorphic construction uses the exists norm alt Sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalDiscreteness/MixedDifference.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalDiscreteness/MixedDifference.lean#L41-L47

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

theorem GroundTheory.Automorphic.exists_norm_altSum_le {ρ : E → F} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hc : HasCompactSupport ρ) (k : ℕ) :
    ∃ B : ℝ, ∀ (v : Fin k → E) (z : E), ‖altSum k ρ v z‖ ≤ B * ∏ i, ‖v i‖ := by sorry
