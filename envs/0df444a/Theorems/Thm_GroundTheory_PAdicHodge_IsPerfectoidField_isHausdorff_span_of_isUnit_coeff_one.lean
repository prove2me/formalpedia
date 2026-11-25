-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isHausdorff_span_of_isUnit_coeff_one
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.isHausdorff_span_of_isUnit_coeff_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:00:42.677971+00:00
-- url     : https://prove2.me/theorems/e73aa1de-4e44-5d54-afcd-b4c8c03a526c
-- title:
--   Is Perfectoid Field: is Hausdorff span of is Unit coeff one
-- statement:
--   The Is Perfectoid Field construction uses the is Hausdorff span of is Unit coeff one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L504-L570
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L504-L570

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.isHausdorff_span_of_isUnit_coeff_one {ξ : 𝕎𝒪♭} (hξ : ξ ∈ RingHom.ker θ)
    (h1 : IsUnit (ξ.coeff 1)) : IsHausdorff (Ideal.span {ξ}) 𝕎𝒪♭ := by sorry
