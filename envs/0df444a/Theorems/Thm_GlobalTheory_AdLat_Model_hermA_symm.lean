-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_Model_hermA_symm
-- name    : GlobalTheory.AdLat.Model.hermA_symm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:54:47.808943+00:00
-- url     : https://prove2.me/theorems/89560770-c839-43ff-ad67-227c7d7fa8cd
-- title:
--   Model: herm A symm
-- statement:
--   The Model construction uses the herm A symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/SmulBasisMemHatIff.lean#L136-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/SmulBasisMemHatIff.lean#L136-L155

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

theorem GlobalTheory.AdLat.Model.hermA_symm (c : E ≃ₐ[F] E) (hc : ∀ x, c (c x) = x) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) E)
    (hG : ∀ a b, c (G a b) = G b a) (x y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.sg _ c (_root_.GlobalTheory.AdLat.hermA c G x y) =
      _root_.GlobalTheory.AdLat.hermA c G y x := by sorry
