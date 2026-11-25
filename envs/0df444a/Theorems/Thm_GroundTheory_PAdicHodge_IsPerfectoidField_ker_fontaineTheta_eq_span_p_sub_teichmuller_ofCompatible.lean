-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_ker_fontaineTheta_eq_span_p_sub_teichmuller_ofCompatible
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.ker_fontaineTheta_eq_span_p_sub_teichmuller_ofCompatible
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:00:57.071715+00:00
-- url     : https://prove2.me/theorems/d3258505-66d8-4114-9df8-d48c81f95d9b
-- title:
--   Is Perfectoid Field: ker fontaine Theta eq span p sub teichmuller of Compatible
-- statement:
--   The Is Perfectoid Field construction uses the ker fontaine Theta eq span p sub teichmuller of Compatible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L395-L398
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L395-L398

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.ker_fontaineTheta_eq_span_p_sub_teichmuller_ofCompatible (y : ℕ → 𝒪)
    (hy : ∀ n, y (n + 1) ^ p = y n) (h0 : y 0 = p) :
    RingHom.ker θ = Ideal.span {(p : 𝕎𝒪♭) - teichmuller p (ofCompatible p y hy)} := by sorry
