-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_fontaineTheta_teichmuller_add_mul_p
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.fontaineTheta_teichmuller_add_mul_p
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:03.550679+00:00
-- url     : https://prove2.me/theorems/428d7382-450d-456b-b011-0cd976352128
-- title:
--   Is Perfectoid Field: fontaine Theta teichmuller add mul p
-- statement:
--   The Is Perfectoid Field construction uses the fontaine Theta teichmuller add mul p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L265-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L265-L267

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.fontaineTheta_teichmuller_add_mul_p (c : 𝒪♭) (v : 𝕎𝒪♭) :
    θ (teichmuller p c + v * p) = PreTilt.untilt c + θ v * p := by sorry
