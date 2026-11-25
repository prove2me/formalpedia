-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_p_pow_mul_mem_of_dvd
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.exists_p_pow_mul_mem_of_dvd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:00:39.566481+00:00
-- url     : https://prove2.me/theorems/641d1e50-56c2-5411-99d8-811047eaffec
-- title:
--   Is Perfectoid Field: exists p pow mul mem of dvd
-- statement:
--   The Is Perfectoid Field construction uses the exists p pow mul mem of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRLattice.lean#L131-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRLattice.lean#L131-L144

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.exists_p_pow_mul_mem_of_dvd {z : 𝕎𝒪♭} {k : ℕ}
    (h : algebraMap 𝕎𝒪♭ 𝔸 (ξ ^ k) ∣ algebraMap 𝕎𝒪♭ 𝔸 z) :
    ∃ s : ℕ, (p : 𝕎𝒪♭) ^ s * z ∈ span {ξ ^ k} := by sorry
