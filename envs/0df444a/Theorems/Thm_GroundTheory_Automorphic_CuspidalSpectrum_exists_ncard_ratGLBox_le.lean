-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CuspidalSpectrum_exists_ncard_ratGLBox_le
-- name    : GroundTheory.Automorphic.CuspidalSpectrum.exists_ncard_ratGLBox_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:33.533359+00:00
-- url     : https://prove2.me/theorems/615edde5-22c0-4dba-8aa6-8a010863f9ba
-- title:
--   Cuspidal Spectrum: exists ncard rat GLBox le
-- statement:
--   The Cuspidal Spectrum construction uses the exists ncard rat GLBox le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalDiscreteness/Counting.lean#L143-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalDiscreteness/Counting.lean#L143-L197

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
variable {K}

theorem GroundTheory.Automorphic.CuspidalSpectrum.exists_ncard_ratGLBox_le (n : ℕ) {𝒦 : Set (FiniteAdeleRing (𝓞 K) K)} (h𝒦 : IsCompact 𝒦) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ T : ℝ, 0 ≤ T →
      (ratGLBox n 𝒦 T).Finite ∧ ((ratGLBox n 𝒦 T).ncard : ℝ) ≤ C * (1 + T) ^ N := by sorry
