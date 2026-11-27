-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_ker_fontaineTheta_eq_span_p_sub_teichmuller
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.exists_ker_fontaineTheta_eq_span_p_sub_teichmuller
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:01:03.931849+00:00
-- url     : https://prove2.me/theorems/db786115-25d3-4e8d-8605-55cfe73ebad4
-- title:
--   Is Perfectoid Field: exists ker fontaine Theta eq span p sub teichmuller
-- statement:
--   The Is Perfectoid Field construction uses the exists ker fontaine Theta eq span p sub teichmuller property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L471-L475
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L471-L475

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.exists_ker_fontaineTheta_eq_span_p_sub_teichmuller [IsAlgClosed K] :
    ∃ pflat : 𝒪♭, PreTilt.untilt pflat = p ∧
      RingHom.ker θ = Ideal.span {(p : 𝕎𝒪♭) - teichmuller p pflat} := by sorry
