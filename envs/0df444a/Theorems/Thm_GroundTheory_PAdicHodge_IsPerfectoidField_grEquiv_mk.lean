-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_grEquiv_mk
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.grEquiv_mk
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:11:17.095621+00:00
-- url     : https://prove2.me/theorems/6ab80793-2fec-4d9d-8a3c-2e43cb74c33d
-- title:
--   Is Perfectoid Field: gr Equiv mk
-- statement:
--   The Is Perfectoid Field construction uses the gr Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRField.lean#L293-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRField.lean#L293-L294

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.grEquiv_mk {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) {i : ℤ} (x : fil K p i) :
    grEquiv hπ i (Submodule.Quotient.mk x) = grMap hπ i x := by sorry
