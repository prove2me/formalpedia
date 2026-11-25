-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_mem_span_xi_pow_of_p_pow_mul_mem
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.mem_span_xi_pow_of_p_pow_mul_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:00:56.129431+00:00
-- url     : https://prove2.me/theorems/d920ccca-59e6-5f17-9ba8-6f762d531cd5
-- title:
--   Is Perfectoid Field: mem span xi pow of p pow mul mem
-- statement:
--   The Is Perfectoid Field construction uses the mem span xi pow of p pow mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRLattice.lean#L68-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRLattice.lean#L68-L91

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_BdRLattice
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
open Ideal WittVector IsLocalRing
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔹" => BDeRhamPlus (normInteger K) p
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt (normInteger K) p))
variable {ξ : WittVector p (PreTilt (normInteger K) p)}

theorem GroundTheory.PAdicHodge.IsPerfectoidField.mem_span_xi_pow_of_p_pow_mul_mem (hξ : RingHom.ker θ = span {ξ}) {x : 𝕎𝒪♭} {s k : ℕ}
    (h : (p : 𝕎𝒪♭) ^ s * x ∈ span {ξ ^ k}) : x ∈ span {ξ ^ k} := by sorry
