-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_mem_ker_isUnit_coeff_one_of_untilt_eq
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.exists_mem_ker_isUnit_coeff_one_of_untilt_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:04.329959+00:00
-- url     : https://prove2.me/theorems/9bbdff76-820f-45a0-babc-ce3b2e1da4e5
-- title:
--   Is Perfectoid Field: exists mem ker is Unit coeff one of untilt eq
-- statement:
--   The Is Perfectoid Field construction uses the exists mem ker is Unit coeff one of untilt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L381-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L381-L385

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open WittVector
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "θ" => fontaineTheta (normInteger K) p

theorem GroundTheory.PAdicHodge.IsPerfectoidField.exists_mem_ker_isUnit_coeff_one_of_untilt_eq {ϖ : 𝒪♭} {u : 𝒪} (hu : IsUnit u)
    (h : PreTilt.untilt ϖ = p * u) :
    ∃ ξ ∈ RingHom.ker θ, IsUnit (ξ.coeff 1) := by sorry
