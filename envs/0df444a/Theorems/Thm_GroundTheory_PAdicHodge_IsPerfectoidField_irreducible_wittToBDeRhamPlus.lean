-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_irreducible_wittToBDeRhamPlus
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.irreducible_wittToBDeRhamPlus
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:54:19.297264+00:00
-- url     : https://prove2.me/theorems/9870ca9f-8064-5997-9f9a-e44ff3a72d79
-- title:
--   Is Perfectoid Field: irreducible witt To BDe Rham Plus
-- statement:
--   The Is Perfectoid Field construction uses the irreducible witt To BDe Rham Plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ThetaPlus.lean#L492-L495
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ThetaPlus.lean#L492-L495

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.irreducible_wittToBDeRhamPlus {ξ : 𝕎𝒪♭} (hξ : RingHom.ker θ = span {ξ}) :
    Irreducible (wittToBDeRhamPlus 𝒪 p ξ) := by sorry
