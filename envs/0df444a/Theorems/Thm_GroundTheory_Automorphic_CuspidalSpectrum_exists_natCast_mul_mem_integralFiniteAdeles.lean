-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CuspidalSpectrum_exists_natCast_mul_mem_integralFiniteAdeles
-- name    : GroundTheory.Automorphic.CuspidalSpectrum.exists_natCast_mul_mem_integralFiniteAdeles
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:29:38.780216+00:00
-- url     : https://prove2.me/theorems/c096bdc7-23a7-46bb-995d-f6d1016e4f7a
-- title:
--   Cuspidal Spectrum: exists nat Cast mul mem integral Finite Adeles
-- statement:
--   The Cuspidal Spectrum construction uses the exists nat Cast mul mem integral Finite Adeles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalDiscreteness/Counting.lean#L27-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalDiscreteness/Counting.lean#L27-L46

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

theorem GroundTheory.Automorphic.CuspidalSpectrum.exists_natCast_mul_mem_integralFiniteAdeles (a : FiniteAdeleRing (𝓞 K) K) :
    ∃ c : ℕ, ((c + 1 : ℕ) : FiniteAdeleRing (𝓞 K) K) * a ∈
      GroundTheory.Global.integralFiniteAdeles (𝓞 K) K := by sorry
