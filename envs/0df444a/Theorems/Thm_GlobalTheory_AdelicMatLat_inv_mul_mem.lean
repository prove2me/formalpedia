-- Prove2me | Theorems.Thm_GlobalTheory_AdelicMatLat_inv_mul_mem
-- name    : GlobalTheory.AdelicMatLat.inv_mul_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:02:20.028797+00:00
-- url     : https://prove2.me/theorems/3b59ce22-3daa-4506-bb34-4b98451e2d55
-- title:
--   Adelic Mat Lat: inv mul mem
-- statement:
--   The Adelic Mat Lat construction uses the inv mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsLatticeAdelicMatrixIntegralTranslate.lean#L137-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsLatticeAdelicMatrixIntegralTranslate.lean#L137-L181

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsLatticeAdelicMatrixIntegralTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.AdelicMatLat
variable (E : Type) [Field E] [NumberField E]
variable {E} {n : ℕ}

theorem GlobalTheory.AdelicMatLat.inv_mul_mem (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (M : ℕ) (δ : GL (Fin n) E)
    (hδ : ∀ x ∈ lat β.1, ∃ y : Fin n → 𝓞 E, (M : E) • x = (fun i => (y i : E)) ᵥ* δ.1)
    (i j : Fin n) :
    (M : FiniteAdeleRing (𝓞 E) E) *
      (β⁻¹.1 * δ⁻¹.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E))) i j ∈ intAdeles E := by sorry
