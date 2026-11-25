-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_Model_smul_basis_mem_hat_iff
-- name    : GlobalTheory.AdLat.Model.smul_basis_mem_hat_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:55:40.431444+00:00
-- url     : https://prove2.me/theorems/34491cb1-4f1e-45f0-8056-ebe3801a767e
-- title:
--   Model: smul basis mem hat iff
-- statement:
--   The Model construction uses the smul basis mem hat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/SmulBasisMemHatIff.lean#L78-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/SmulBasisMemHatIff.lean#L78-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_SmulBasisMemHatIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Model
open NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem GlobalTheory.AdLat.Model.smul_basis_mem_hat_iff {n : ℕ} {ι : Type} (b : Module.Basis ι F (Fin n → E)) (j : ι) (t : F) :
    fv F (t • b j) ∈ hat F (freeLat b) ↔ t ∈ (algebraMap (𝓞 F) F).range := by sorry
