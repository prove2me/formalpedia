-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_Model_sg_tmul
-- name    : GlobalTheory.AdLat.Model.sg_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:48:11.411633+00:00
-- url     : https://prove2.me/theorems/8642e55c-d1e4-421a-8763-0268162b0d17
-- title:
--   Model: sg tmul
-- statement:
--   The Model construction uses the sg tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/SmulBasisMemHatIff.lean#L95-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/SmulBasisMemHatIff.lean#L95-L97

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
open NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem GlobalTheory.AdLat.Model.sg_tmul (c : E ≃ₐ[F] E) (a : FiniteAdeleRing (𝓞 F) F) (x : E) :
    _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (a ⊗ₜ x) = a ⊗ₜ c x := by sorry
