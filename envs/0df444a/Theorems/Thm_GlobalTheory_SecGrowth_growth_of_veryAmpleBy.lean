-- Prove2me | Theorems.Thm_GlobalTheory_SecGrowth_growth_of_veryAmpleBy
-- name    : GlobalTheory.SecGrowth.growth_of_veryAmpleBy
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:30.072853+00:00
-- url     : https://prove2.me/theorems/dcf7682c-ac50-4342-bbbc-6d3c461afdf6
-- title:
--   Sec Growth: growth of very Ample By
-- statement:
--   The Sec Growth construction uses the growth of very Ample By property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteOfNotLinearIndependent.lean#L99-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteOfNotLinearIndependent.lean#L99-L205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIndepSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteOfNotLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.SecGrowth

theorem GlobalTheory.SecGrowth.growth_of_veryAmpleBy {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) {H : LB X} {m : ℕ} (s : Fin (m + 1) → LB.Sec H) (hs : VeryAmpleBy f H s)
    (g t₀ : ℕ)
    (hgen : ∀ t : ℕ, t₀ ≤ t → ∀ σ : LB.Sec (pw H t), ∃ F : MvPolynomial (Fin (m + 1)) K, F.IsHomogeneous t ∧
      ∀ k : H.ι, σ.f k = MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) F)
    (hGK : ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra K B] (r : Fin (m + 1) → B),
      Function.Surjective (MvPolynomial.aeval r : MvPolynomial (Fin (m + 1)) K →ₐ[K] B) → Algebra.trdeg K B = g →
      ∃ c C : ℕ, 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t →
        t ^ g ≤ c * Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin (m + 1)) K t).map
          (MvPolynomial.aeval r : MvPolynomial (Fin (m + 1)) K →ₐ[K] B).toLinearMap) ∧
        Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin (m + 1)) K t).map
          (MvPolynomial.aeval r : MvPolynomial (Fin (m + 1)) K →ₐ[K] B).toLinearMap) ≤ C * t ^ g)
    (htr : ∀ (B : Type) [CommRing B] [Nontrivial B] [Algebra K B] (j : Spec (CommRingCat.of B) ⟶ X),
      IsOpenImmersion j → j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K B)) → Algebra.trdeg K B = g)
    (V : ℕ → Type) [∀ t, AddCommGroup (V t)] [∀ t, Module K (V t)] [∀ t, Module.Finite K (V t)]
    (ev : ∀ t : ℕ, V t → LB.Sec (pw H t))
    (hadd : ∀ t a b (k : H.ι), (ev t (a + b)).f k = (ev t a).f k + (ev t b).f k)
    (hsmul : ∀ t (c : K) a (k : H.ι), (ev t (c • a)).f k = cst f (H.U k) c * (show Γ(X, H.U k) from (ev t a).f k))
    (hinj : ∀ t a, (∀ k : H.ι, (ev t a).f k = 0) → a = 0)
    (hsurj : ∀ (t : ℕ) (σ : LB.Sec (pw H t)), ∃ a, ∀ k : H.ι, (ev t a).f k = σ.f k) :
    ∃ c C : ℕ, 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t →
      t ^ g ≤ c * Module.finrank K (V t) ∧ Module.finrank K (V t) ≤ C * t ^ g := by sorry
