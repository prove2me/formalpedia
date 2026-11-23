-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_inv_mulVec_mem_hat
-- name    : GlobalTheory.AdLat.inv_mulVec_mem_hat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:01.924076+00:00
-- url     : https://prove2.me/theorems/ec7a476d-1f2e-40cd-8274-6576a9799d01
-- title:
--   Ad Lat: inv mul Vec mem hat
-- statement:
--   The Ad Lat construction uses the inv mul Vec mem hat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CramerMemAdelicCompletionOfElementSet.lean#L69-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CramerMemAdelicCompletionOfElementSet.lean#L69-L137

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemAdelicCompletionPseudoBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat

theorem GlobalTheory.AdLat.inv_mulVec_mem_hat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) (RA F E)) (c : E ≃ₐ[F] E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ z ∈ (hat F (L : Set (Fin n → E))), (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ z ∈ (hat F (L : Set (Fin n → E)))) → (g : Matrix (Fin n) (Fin n) (RA F E)).det * sg (FiniteAdeleRing (𝓞 F) F) c (g : Matrix (Fin n) (Fin n) (RA F E)).det = 1 → ∀ z ∈ (hat F (L : Set (Fin n → E))), ((g⁻¹ : GL (Fin n) (RA F E)) : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ z ∈ (hat F (L : Set (Fin n → E))) := by sorry
