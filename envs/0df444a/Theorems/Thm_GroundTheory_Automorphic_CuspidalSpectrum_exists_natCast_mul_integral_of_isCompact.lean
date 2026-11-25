-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CuspidalSpectrum_exists_natCast_mul_integral_of_isCompact
-- name    : GroundTheory.Automorphic.CuspidalSpectrum.exists_natCast_mul_integral_of_isCompact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:18.546476+00:00
-- url     : https://prove2.me/theorems/06678f7b-8171-45a3-8231-54a0e91950f7
-- title:
--   Cuspidal Spectrum: exists nat Cast mul integral of is Compact
-- statement:
--   The Cuspidal Spectrum construction uses the exists nat Cast mul integral of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalDiscreteness/Counting.lean#L48-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalDiscreteness/Counting.lean#L48-L68

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

theorem GroundTheory.Automorphic.CuspidalSpectrum.exists_natCast_mul_integral_of_isCompact {𝒦 : Set (FiniteAdeleRing (𝓞 K) K)}
    (h𝒦 : IsCompact 𝒦) :
    ∃ m : ℕ, 0 < m ∧ ∀ ξ : K, algebraMap K (FiniteAdeleRing (𝓞 K) K) ξ ∈ 𝒦 →
      ∃ z : 𝓞 K, (z : K) = m * ξ := by sorry
