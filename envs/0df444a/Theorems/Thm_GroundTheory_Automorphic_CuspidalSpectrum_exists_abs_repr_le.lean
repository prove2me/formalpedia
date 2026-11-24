-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CuspidalSpectrum_exists_abs_repr_le
-- name    : GroundTheory.Automorphic.CuspidalSpectrum.exists_abs_repr_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:29:28.561615+00:00
-- url     : https://prove2.me/theorems/b3538909-6cd5-4e29-8a02-acbcca77dce0
-- title:
--   Cuspidal Spectrum: exists abs repr le
-- statement:
--   The Cuspidal Spectrum construction uses the exists abs repr le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalDiscreteness/Counting.lean#L72-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalDiscreteness/Counting.lean#L72-L85

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
open scoped Classical

theorem GroundTheory.Automorphic.CuspidalSpectrum.exists_abs_repr_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : 𝓞 K) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 K)),
      |(((RingOfIntegers.basis K).repr z i : ℤ) : ℝ)| ≤
        C * ‖mixedEmbedding K (z : K)‖ := by sorry
