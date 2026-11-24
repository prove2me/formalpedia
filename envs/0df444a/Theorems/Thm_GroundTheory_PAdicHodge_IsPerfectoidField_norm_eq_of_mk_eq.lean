-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_norm_eq_of_mk_eq
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.norm_eq_of_mk_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:29.603904+00:00
-- url     : https://prove2.me/theorems/cc801dd9-a54c-4dfa-8efe-d2f4ab75dc3d
-- title:
--   Is Perfectoid Field: norm eq of mk eq
-- statement:
--   The Is Perfectoid Field construction uses the norm eq of mk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L131-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L131-L142

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
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
variable {p}
omit [Fact p.Prime] [IsPerfectoidField K p]
variable (p)

theorem GroundTheory.PAdicHodge.IsPerfectoidField.norm_eq_of_mk_eq {b c : 𝒪}
    (h : Ideal.Quotient.mk (Ideal.span {(p : 𝒪)}) b = Ideal.Quotient.mk _ c)
    (hc : ‖(p : K)‖ < ‖(c : K)‖) : ‖(b : K)‖ = ‖(c : K)‖ := by sorry
