-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_eq_zero_of_teichmuller_mul_eq_zero
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.eq_zero_of_teichmuller_mul_eq_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:00:58.93632+00:00
-- url     : https://prove2.me/theorems/cfbb8a87-b57f-4735-b9b7-e8a5b9e060f9
-- title:
--   Is Perfectoid Field: eq zero of teichmuller mul eq zero
-- statement:
--   The Is Perfectoid Field construction uses the eq zero of teichmuller mul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L490-L494
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L490-L494

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.eq_zero_of_teichmuller_mul_eq_zero {ϖ : 𝒪♭} (hϖ : ϖ ≠ 0) {x : 𝕎𝒪♭}
    (h : teichmuller p ϖ * x = 0) : x = 0 := by sorry
