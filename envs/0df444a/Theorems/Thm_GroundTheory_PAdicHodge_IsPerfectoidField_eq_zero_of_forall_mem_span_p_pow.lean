-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_eq_zero_of_forall_mem_span_p_pow
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.eq_zero_of_forall_mem_span_p_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:00:47.786434+00:00
-- url     : https://prove2.me/theorems/0d771260-6c61-531c-a01b-10072fa71047
-- title:
--   Is Perfectoid Field: eq zero of forall mem span p pow
-- statement:
--   The Is Perfectoid Field construction uses the eq zero of forall mem span p pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRLattice.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRLattice.lean#L52-L56

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
omit [CharZero K]

theorem GroundTheory.PAdicHodge.IsPerfectoidField.eq_zero_of_forall_mem_span_p_pow {b : 𝒪} (h : ∀ M : ℕ, b ∈ span {(p : 𝒪) ^ M}) : b = 0 := by sorry
