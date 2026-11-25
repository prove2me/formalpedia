-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_Model_fv_mulVec
-- name    : GlobalTheory.AdLat.Model.fv_mulVec
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:54:32.813635+00:00
-- url     : https://prove2.me/theorems/e1d92e14-66e7-5e8c-98f9-22e095534cdb
-- title:
--   Model: fv mul Vec
-- statement:
--   The Model construction uses the fv mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/SmulBasisMemHatIff.lean#L157-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/SmulBasisMemHatIff.lean#L157-L160

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

theorem GlobalTheory.AdLat.Model.fv_mulVec {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    (γ.map fun e => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e : RA F E)).mulVec (fv F x) = fv F (γ.mulVec x) := by sorry
