-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CuspidalSpectrum_exists_ncard_integers_le
-- name    : GroundTheory.Automorphic.CuspidalSpectrum.exists_ncard_integers_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:48.876949+00:00
-- url     : https://prove2.me/theorems/ab9d180a-69c0-48bc-ac80-401687521d54
-- title:
--   Cuspidal Spectrum: exists ncard integers le
-- statement:
--   The Cuspidal Spectrum construction uses the exists ncard integers le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalDiscreteness/Counting.lean#L87-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalDiscreteness/Counting.lean#L87-L135

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalDiscreteness_Counting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Set
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.CuspidalSpectrum
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Automorphic.CuspidalSpectrum.exists_ncard_integers_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      {z : 𝓞 K | ∀ w : InfinitePlace K, w (z : K) ≤ T}.Finite ∧
      (({z : 𝓞 K | ∀ w : InfinitePlace K, w (z : K) ≤ T}.ncard : ℝ) ≤
        C * (1 + T) ^ Module.finrank ℚ K) := by sorry
