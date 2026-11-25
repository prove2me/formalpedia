-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_grMap_smul
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.grMap_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:01:14.119439+00:00
-- url     : https://prove2.me/theorems/39ff9770-2577-5e0d-949f-8ed2ccac67d7
-- title:
--   Is Perfectoid Field: gr Map smul
-- statement:
--   The Is Perfectoid Field construction uses the gr Map smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRField.lean#L260-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRField.lean#L260-L262

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.grMap_smul {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) {i : ℤ} (c : 𝔹) (x : fil K p i) :
    grMap hπ i (c • x) = thetaBDeRhamPlusField p c * grMap hπ i x := by sorry
