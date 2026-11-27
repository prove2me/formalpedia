-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_mem_nonZeroDivisors_of_isUnit_coeff_one
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.mem_nonZeroDivisors_of_isUnit_coeff_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:00:56.585821+00:00
-- url     : https://prove2.me/theorems/68b923a7-4f4d-5496-82dd-42daac3344d0
-- title:
--   Is Perfectoid Field: mem non Zero Divisors of is Unit coeff one
-- statement:
--   The Is Perfectoid Field construction uses the mem non Zero Divisors of is Unit coeff one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L496-L502
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L496-L502

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.mem_nonZeroDivisors_of_isUnit_coeff_one {ξ : 𝕎𝒪♭} (h1 : IsUnit (ξ.coeff 1)) :
    ξ ∈ nonZeroDivisors 𝕎𝒪♭ := by sorry
