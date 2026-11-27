-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_algebraMap_mem_fil_iff
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.algebraMap_mem_fil_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:01:51.229829+00:00
-- url     : https://prove2.me/theorems/e17761cc-0e15-53e4-865b-565a37da621a
-- title:
--   Is Perfectoid Field: algebra Map mem fil iff
-- statement:
--   The Is Perfectoid Field construction uses the algebra Map mem fil iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRField.lean#L164-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRField.lean#L164-L173

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRGalois
import Definitions.Def_GroundTheory_PAdicHodge_BdRField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Ideal WittVector IsLocalRing
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt (normInteger K) p))
local notation "𝔹" => BDeRhamPlus (normInteger K) p
local notation "𝔹dR" => BDeRham (normInteger K) p
local notation "J" => RingHom.ker (fontaineThetaInvertP (normInteger K) p)

theorem GroundTheory.PAdicHodge.IsPerfectoidField.algebraMap_mem_fil_iff (b : 𝔹) (n : ℕ) :
    algebraMap 𝔹 𝔹dR b ∈ fil K p n ↔ b ∈ maximalIdeal 𝔹 ^ n := by sorry
