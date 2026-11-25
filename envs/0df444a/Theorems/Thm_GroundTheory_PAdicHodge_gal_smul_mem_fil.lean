-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_gal_smul_mem_fil
-- name    : GroundTheory.PAdicHodge.gal_smul_mem_fil
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:54:35.745568+00:00
-- url     : https://prove2.me/theorems/e7ce5dc8-7360-4b77-a072-e5c5466c6df2
-- title:
--   PAdic Hodge: gal smul mem fil
-- statement:
--   The PAdic Hodge construction uses the gal smul mem fil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRField.lean#L355-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRField.lean#L355-L360

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

theorem GroundTheory.PAdicHodge.gal_smul_mem_fil (σ : Gal(PadicAlgCl p/L)) {i : ℤ} {x : 𝔹dR}
    (hx : x ∈ IsPerfectoidField.fil ℂ_[p] p i) : σ • x ∈ IsPerfectoidField.fil ℂ_[p] p i := by sorry
