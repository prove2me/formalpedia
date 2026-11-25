-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_gal_smul_bDeRham_def
-- name    : GroundTheory.PAdicHodge.gal_smul_bDeRham_def
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:54:41.157808+00:00
-- url     : https://prove2.me/theorems/07cb6c05-bca0-4ee3-b00e-e748fc31ff3e
-- title:
--   PAdic Hodge: gal smul b De Rham def
-- statement:
--   The PAdic Hodge construction uses the gal smul b De Rham def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRField.lean#L340-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRField.lean#L340-L341

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

theorem GroundTheory.PAdicHodge.gal_smul_bDeRham_def (σ : Gal(PadicAlgCl p/L)) (x : 𝔹dR) : σ • x = galBdRField σ x := by sorry
