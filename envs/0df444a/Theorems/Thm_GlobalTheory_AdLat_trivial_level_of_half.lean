-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_trivial_level_of_half
-- name    : GlobalTheory.AdLat.trivial_level_of_half
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:35:12.970462+00:00
-- url     : https://prove2.me/theorems/6037bc12-c968-4620-b32f-f1a13d101466
-- title:
--   Ad Lat: trivial level of half
-- statement:
--   The Ad Lat construction uses the trivial level of half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IntegralTmulOneMulMemAdelicCompletion.lean#L129-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IntegralTmulOneMulMemAdelicCompletion.lean#L129-L227

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionSelfDualOfSelfDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralTmulOneMulMemAdelicCompletion
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
open Half
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors

theorem GlobalTheory.AdLat.trivial_level_of_half : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (c : E ≃ₐ[F] E)
    (G : Matrix (Fin n) (Fin n) E) (J : FractionalIdeal (𝓞 E)⁰ E)
    (g : GL (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) (M : ℕ) (I I' : Ideal (𝓞 E)), L.FG →
    Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ x, c (c x) = x) → (∀ a b, c (G a b) = G b a) →
    G.det ≠ 0 → J ≠ 0 → (∀ v : Fin n → E, (∀ y ∈ L, (∑ a, ∑ b, v a * G a b * c (y b)) ∈ J) ↔ v ∈ L) →
    (∀ x y, _root_.GlobalTheory.AdLat.hermA c G ((g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) *ᵥ x)
      ((g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) *ᵥ y) = _root_.GlobalTheory.AdLat.hermA c G x y) →
    0 < M → I ⊔ I' = ⊤ → I * I' = Ideal.span {(M : 𝓞 E)} →
    (∀ b ∈ I', ∃ b' ∈ I, ((b' : 𝓞 E) : E) = c (b : E)) →
    (∀ b ∈ I, ∀ z ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
      ∃ y ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
        (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) *ᵥ
          (fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) * z i) -
          (fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) * z i) = M • y) →
    ∀ z ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
      ∃ y ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
        (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) *ᵥ z - z = M • y := by sorry
