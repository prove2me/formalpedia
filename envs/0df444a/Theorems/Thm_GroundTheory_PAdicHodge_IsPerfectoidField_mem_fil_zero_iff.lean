-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_mem_fil_zero_iff
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.mem_fil_zero_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:53:12.156137+00:00
-- url     : https://prove2.me/theorems/6bf8b1c0-f933-5702-b3aa-f2fc30487ea0
-- title:
--   Is Perfectoid Field: mem fil zero iff
-- statement:
--   The Is Perfectoid Field construction uses the mem fil zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRField.lean#L160-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRField.lean#L160-L162

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
variable (K p)

theorem GroundTheory.PAdicHodge.IsPerfectoidField.mem_fil_zero_iff {x : 𝔹dR} : x ∈ fil K p 0 ↔ ∃ b : 𝔹, x = algebraMap 𝔹 𝔹dR b := by sorry
