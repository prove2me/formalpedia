-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_gal_smul_mem_fil_iff
-- name    : GroundTheory.PAdicHodge.gal_smul_mem_fil_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:02:07.076464+00:00
-- url     : https://prove2.me/theorems/ca8ec1f3-b85e-57f2-8561-e7d217631254
-- title:
--   PAdic Hodge: gal smul mem fil iff
-- statement:
--   The PAdic Hodge construction uses the gal smul mem fil iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRField.lean#L362-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRField.lean#L362-L366

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

theorem GroundTheory.PAdicHodge.gal_smul_mem_fil_iff (σ : Gal(PadicAlgCl p/L)) (i : ℤ) (x : 𝔹dR) :
    σ • x ∈ IsPerfectoidField.fil ℂ_[p] p i ↔ x ∈ IsPerfectoidField.fil ℂ_[p] p i := by sorry
