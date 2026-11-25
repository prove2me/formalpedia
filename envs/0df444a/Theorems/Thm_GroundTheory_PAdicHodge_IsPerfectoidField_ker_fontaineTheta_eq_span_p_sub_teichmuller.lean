-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_ker_fontaineTheta_eq_span_p_sub_teichmuller
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.ker_fontaineTheta_eq_span_p_sub_teichmuller
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:00.616126+00:00
-- url     : https://prove2.me/theorems/49c32639-ae72-44c3-a0c5-a77b3249eb33
-- title:
--   Is Perfectoid Field: ker fontaine Theta eq span p sub teichmuller
-- statement:
--   The Is Perfectoid Field construction uses the ker fontaine Theta eq span p sub teichmuller property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L387-L393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L387-L393

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.ker_fontaineTheta_eq_span_p_sub_teichmuller {pflat : 𝒪♭}
    (h : PreTilt.untilt pflat = p) :
    RingHom.ker θ = Ideal.span {(p : 𝕎𝒪♭) - teichmuller p pflat} := by sorry
