-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_gal_smul_algebraMap_bDeRham
-- name    : GroundTheory.PAdicHodge.gal_smul_algebraMap_bDeRham
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:59:24.595535+00:00
-- url     : https://prove2.me/theorems/e5aff2aa-2d80-55e4-a503-0e7f27cb4149
-- title:
--   PAdic Hodge: gal smul algebra Map b De Rham
-- statement:
--   The PAdic Hodge construction uses the gal smul algebra Map b De Rham property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRField.lean#L343-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRField.lean#L343-L345

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

theorem GroundTheory.PAdicHodge.gal_smul_algebraMap_bDeRham (σ : Gal(PadicAlgCl p/L)) (b : 𝔹) :
    σ • algebraMap 𝔹 𝔹dR b = algebraMap 𝔹 𝔹dR (σ • b) := by sorry
