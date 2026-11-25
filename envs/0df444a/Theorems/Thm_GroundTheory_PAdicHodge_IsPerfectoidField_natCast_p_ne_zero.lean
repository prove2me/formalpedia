-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_natCast_p_ne_zero
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.natCast_p_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:01:45.687363+00:00
-- url     : https://prove2.me/theorems/8af987c9-d5ce-475e-b007-d770f19b06f0
-- title:
--   Is Perfectoid Field: nat Cast p ne zero
-- statement:
--   The Is Perfectoid Field construction uses the nat Cast p ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRLattice.lean#L60-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRLattice.lean#L60-L64

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
omit [IsPerfectoidField K p]

theorem GroundTheory.PAdicHodge.IsPerfectoidField.natCast_p_ne_zero : (p : 𝒪) ≠ 0 := by sorry
