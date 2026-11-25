-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CuspidalSpectrum_exists_pos_natCast_mul_isIntegral
-- name    : GroundTheory.Automorphic.CuspidalSpectrum.exists_pos_natCast_mul_isIntegral
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:29:39.165802+00:00
-- url     : https://prove2.me/theorems/c2b4bf6c-1296-4dc4-b53e-018681b546c6
-- title:
--   Cuspidal Spectrum: exists pos nat Cast mul is Integral
-- statement:
--   The Cuspidal Spectrum construction uses the exists pos nat Cast mul is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalDiscreteness/Counting.lean#L14-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalDiscreteness/Counting.lean#L14-L25

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

theorem GroundTheory.Automorphic.CuspidalSpectrum.exists_pos_natCast_mul_isIntegral (k : K) : ∃ c : ℕ, 0 < c ∧ IsIntegral ℤ ((c : K) * k) := by sorry
