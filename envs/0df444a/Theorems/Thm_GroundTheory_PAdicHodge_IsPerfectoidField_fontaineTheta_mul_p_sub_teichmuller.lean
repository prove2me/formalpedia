-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_fontaineTheta_mul_p_sub_teichmuller
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.fontaineTheta_mul_p_sub_teichmuller
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:02.911902+00:00
-- url     : https://prove2.me/theorems/f19588d9-79d4-4f03-ba64-35aeeee0e86b
-- title:
--   Is Perfectoid Field: fontaine Theta mul p sub teichmuller
-- statement:
--   The Is Perfectoid Field construction uses the fontaine Theta mul p sub teichmuller property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L356-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L356-L359

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.fontaineTheta_mul_p_sub_teichmuller {ϖ : 𝒪♭} {w : 𝕎𝒪♭}
    (h : PreTilt.untilt ϖ = p * θ w) : w * p - teichmuller p ϖ ∈ RingHom.ker θ := by sorry
