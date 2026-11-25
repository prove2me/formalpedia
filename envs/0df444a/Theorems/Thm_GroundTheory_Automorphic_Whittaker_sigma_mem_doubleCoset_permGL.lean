-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigma_mem_doubleCoset_permGL
-- name    : GroundTheory.Automorphic.Whittaker.sigma_mem_doubleCoset_permGL
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:34:47.656805+00:00
-- url     : https://prove2.me/theorems/bec16d5e-83be-47ee-ae0b-533544cd9a0f
-- title:
--   Whittaker: sigma mem double Coset perm GL
-- statement:
--   The Whittaker construction uses the sigma mem double Coset perm GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L276-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L276-L282

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable (ψ₀ : AddChar F ℂ)

theorem GroundTheory.Automorphic.Whittaker.sigma_mem_doubleCoset_permGL {g : GL (Fin n) F} {w : Equiv.Perm (Fin n)}
    (hg : g ∈ doubleCoset (permGL F w) (borel n F : Set (GL (Fin n) F)) (borel n F)) :
    sigma g ∈ doubleCoset (permGL F (Fin.revPerm * w⁻¹ * Fin.revPerm))
      (borel n F : Set (GL (Fin n) F)) (borel n F) := by sorry
