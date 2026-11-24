-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_eq_zero_of_p_mul_eq_zero
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.eq_zero_of_p_mul_eq_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:51:26.75544+00:00
-- url     : https://prove2.me/theorems/4a8f84c5-ac20-4fad-be87-252cc27a3386
-- title:
--   Is Perfectoid Field: eq zero of p mul eq zero
-- statement:
--   The Is Perfectoid Field construction uses the eq zero of p mul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L487-L488
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L487-L488

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.eq_zero_of_p_mul_eq_zero {x : 𝕎𝒪♭} (h : (p : 𝕎𝒪♭) * x = 0) : x = 0 := by sorry
