-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_norm_untilt_coeff_zero
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.norm_untilt_coeff_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:21.894144+00:00
-- url     : https://prove2.me/theorems/bedb7942-fe87-4994-ae2d-4f617ac1f1c8
-- title:
--   Is Perfectoid Field: norm untilt coeff zero
-- statement:
--   The Is Perfectoid Field construction uses the norm untilt coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L290-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L290-L298

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.norm_untilt_coeff_zero {ξ v : 𝕎𝒪♭} (hξ : ξ ∈ RingHom.ker θ)
    (hv : ξ = teichmuller p (ξ.coeff 0) + v * p) :
    ‖((PreTilt.untilt (ξ.coeff 0) : 𝒪) : K)‖ = ‖((θ v : 𝒪) : K)‖ * ‖(p : K)‖ := by sorry
