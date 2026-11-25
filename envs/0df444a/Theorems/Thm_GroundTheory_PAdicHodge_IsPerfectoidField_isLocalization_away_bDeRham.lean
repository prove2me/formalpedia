-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isLocalization_away_bDeRham
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.isLocalization_away_bDeRham
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:53:44.926517+00:00
-- url     : https://prove2.me/theorems/f13908c4-7200-5a7a-b7e8-f22c093f6d64
-- title:
--   Is Perfectoid Field: is Localization away b De Rham
-- statement:
--   The Is Perfectoid Field construction uses the is Localization away b De Rham property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRField.lean#L98-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRField.lean#L98-L113

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.isLocalization_away_bDeRham {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) :
    IsLocalization.Away π 𝔹dR := by sorry
