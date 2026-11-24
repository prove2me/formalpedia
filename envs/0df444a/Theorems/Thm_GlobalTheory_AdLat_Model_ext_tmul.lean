-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_Model_ext_tmul
-- name    : GlobalTheory.AdLat.Model.ext_tmul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:53:24.318258+00:00
-- url     : https://prove2.me/theorems/9d74310c-0012-4210-a008-d542956d0b1d
-- title:
--   Model: ext tmul
-- statement:
--   The Model construction uses the ext tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/SmulBasisMemHatIff.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/SmulBasisMemHatIff.lean#L39-L44

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

theorem GlobalTheory.AdLat.Model.ext_tmul {n : ℕ} (φ : (Fin n → E) →ₗ[F] F) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    ext φ (fun i => a ⊗ₜ x i) = algebraMap F _ (φ x) * a := by sorry
