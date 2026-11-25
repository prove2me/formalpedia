-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_maximalIdeal_eq_span_gal_smul
-- name    : GroundTheory.PAdicHodge.maximalIdeal_eq_span_gal_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:02:51.014367+00:00
-- url     : https://prove2.me/theorems/2d606650-01db-498a-ba93-cee59398be6f
-- title:
--   PAdic Hodge: maximal Ideal eq span gal smul
-- statement:
--   The PAdic Hodge construction uses the maximal Ideal eq span gal smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRField.lean#L347-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRField.lean#L347-L353

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
variable {p : ℕ} [Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

theorem GroundTheory.PAdicHodge.maximalIdeal_eq_span_gal_smul (σ : Gal(PadicAlgCl p/L)) {π : 𝔹}
    (hπ : maximalIdeal 𝔹 = span {π}) : maximalIdeal 𝔹 = span {σ • π} := by sorry
