-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_residueFieldBDeRhamPlusEquiv_residue
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.residueFieldBDeRhamPlusEquiv_residue
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:01:14.860184+00:00
-- url     : https://prove2.me/theorems/96c19032-9340-4b7c-a1f0-a57823b00c16
-- title:
--   Is Perfectoid Field: residue Field BDe Rham Plus Equiv residue
-- statement:
--   The Is Perfectoid Field construction uses the residue Field BDe Rham Plus Equiv residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ThetaPlus.lean#L505-L507
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ThetaPlus.lean#L505-L507

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
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
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔹" => BDeRhamPlus (normInteger K) p
variable {p}
variable [CharZero K]

theorem GroundTheory.PAdicHodge.IsPerfectoidField.residueFieldBDeRhamPlusEquiv_residue (x : 𝔹) :
    residueFieldBDeRhamPlusEquiv (residue 𝔹 x) = thetaBDeRhamPlusField p x := by sorry
