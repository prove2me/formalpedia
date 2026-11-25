-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_Model_latOf_rational
-- name    : GlobalTheory.AdLat.Model.latOf_rational
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:54:57.21775+00:00
-- url     : https://prove2.me/theorems/5e7c1ae5-5b04-419d-ada6-a763b9051534
-- title:
--   Model: lat Of rational
-- statement:
--   The Model construction uses the lat Of rational property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/SmulBasisMemHatIff.lean#L162-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/SmulBasisMemHatIff.lean#L162-L183

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

theorem GlobalTheory.AdLat.Model.latOf_rational {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) :
    latOf F (γ.map fun e => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e : RA F E)) L = latOf F 1 (γ.mulVec '' L) := by sorry
