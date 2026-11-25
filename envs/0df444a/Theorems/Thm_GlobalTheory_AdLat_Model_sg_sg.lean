-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_Model_sg_sg
-- name    : GlobalTheory.AdLat.Model.sg_sg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:54:46.62701+00:00
-- url     : https://prove2.me/theorems/8a04b7c7-9699-575d-a73b-77a4592f6058
-- title:
--   Model: sg sg
-- statement:
--   The Model construction uses the sg sg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/SmulBasisMemHatIff.lean#L126-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/SmulBasisMemHatIff.lean#L126-L130

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

theorem GlobalTheory.AdLat.Model.sg_sg (c : E ≃ₐ[F] E) (hc : ∀ x, c (c x) = x) (z : RA F E) : sg _ c (sg _ c z) = z := by sorry
