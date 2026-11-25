-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_coeff_zero_add_eq_zero
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.untilt_coeff_zero_add_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:36.785797+00:00
-- url     : https://prove2.me/theorems/2c93a103-9d57-46d0-832d-2e602f119b67
-- title:
--   Is Perfectoid Field: untilt coeff zero add eq zero
-- statement:
--   The Is Perfectoid Field construction uses the untilt coeff zero add eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L284-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L284-L288

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.untilt_coeff_zero_add_eq_zero {ξ v : 𝕎𝒪♭} (hξ : ξ ∈ RingHom.ker θ)
    (hv : ξ = teichmuller p (ξ.coeff 0) + v * p) :
    PreTilt.untilt (ξ.coeff 0) + θ v * p = 0 := by sorry
