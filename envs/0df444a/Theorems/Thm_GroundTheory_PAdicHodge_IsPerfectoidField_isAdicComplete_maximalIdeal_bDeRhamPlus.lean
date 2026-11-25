-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isAdicComplete_maximalIdeal_bDeRhamPlus
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.isAdicComplete_maximalIdeal_bDeRhamPlus
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:59:16.709857+00:00
-- url     : https://prove2.me/theorems/28857df2-6d3f-5c90-86d8-a3ea00351238
-- title:
--   Is Perfectoid Field: is Adic Complete maximal Ideal b De Rham Plus
-- statement:
--   The Is Perfectoid Field construction uses the is Adic Complete maximal Ideal b De Rham Plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ThetaPlus.lean#L497-L499
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ThetaPlus.lean#L497-L499

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.isAdicComplete_maximalIdeal_bDeRhamPlus : IsAdicComplete (maximalIdeal 𝔹) 𝔹 := by sorry
