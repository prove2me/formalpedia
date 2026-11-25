-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_mem_span_xi_pow_of_forall_mem_sup
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.mem_span_xi_pow_of_forall_mem_sup
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:01:43.340792+00:00
-- url     : https://prove2.me/theorems/9cb88cff-9d71-4277-a4df-52ef992ba401
-- title:
--   Is Perfectoid Field: mem span xi pow of forall mem sup
-- statement:
--   The Is Perfectoid Field construction uses the mem span xi pow of forall mem sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRLattice.lean#L93-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRLattice.lean#L93-L129

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.mem_span_xi_pow_of_forall_mem_sup (hξ : RingHom.ker θ = span {ξ}) {x : 𝕎𝒪♭} {k : ℕ}
    (h : ∀ M : ℕ, x ∈ span {(p : 𝕎𝒪♭) ^ M} ⊔ span {ξ ^ k}) : x ∈ span {ξ ^ k} := by sorry
