-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_mem_ker_fontaineTheta_isUnit_coeff_one
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.exists_mem_ker_fontaineTheta_isUnit_coeff_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:52.217794+00:00
-- url     : https://prove2.me/theorems/53920598-1fc2-4826-90e5-569f4493a55b
-- title:
--   Is Perfectoid Field: exists mem ker fontaine Theta is Unit coeff one
-- statement:
--   The Is Perfectoid Field construction uses the exists mem ker fontaine Theta is Unit coeff one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L440-L443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L440-L443

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
variable (K p)

theorem GroundTheory.PAdicHodge.IsPerfectoidField.exists_mem_ker_fontaineTheta_isUnit_coeff_one :
    ∃ ξ ∈ RingHom.ker θ, IsUnit (ξ.coeff 1) := by sorry
