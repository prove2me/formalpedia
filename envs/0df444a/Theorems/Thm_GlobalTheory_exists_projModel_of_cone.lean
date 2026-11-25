-- Prove2me | Theorems.Thm_GlobalTheory_exists_projModel_of_cone
-- name    : GlobalTheory.exists_projModel_of_cone
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:34:34.70502+00:00
-- url     : https://prove2.me/theorems/5c8e303f-fac2-5b1a-bfb9-4e4e2c928346
-- title:
--   Global Theory: exists proj Model of cone
-- statement:
--   The Global Theory construction uses the exists proj Model of cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsProjectiveModelPolarisedTorusTheta.lean#L155-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsProjectiveModelPolarisedTorusTheta.lean#L155-L370

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AlgebraMapZeroSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsProjectiveModelPolarisedTorusTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory

theorem GlobalTheory.exists_projModel_of_cone
    (h1 : ∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ,
      (∀ a, e (constFn X.hom U a) = a) →
      ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f)
    {σ E : Type} [Fintype σ] [NormedAddCommGroup E] [NormedSpace ℂ E] (f : σ → E → ℂ)
    (hf : ∀ c, Differentiable ℂ (f c)) (hne : ∀ z, ∃ c, f c z ≠ 0) (I : Ideal (MvPolynomial σ ℂ))
    (hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : E), MvPolynomial.eval (fun c => t * f c z) F = 0)
    (hP : I.IsPrime) (g : ℕ) (hg : ringKrullDim (MvPolynomial σ ℂ ⧸ I) ≤ (g + 1 : ℕ))
    (hZ : ∀ p : σ → ℂ, (∀ F ∈ I, MvPolynomial.eval p F = 0) → ∃ (t : ℂ) (z : E), p = fun c => t * f c z) :
    ∃ (X : Over (Sp ℂ)) (ex : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : σ → X.left.Opens),
      IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧
      (∀ z z', ex z = ex z' ↔ ∃ gam : ℂ, ∀ c, f c z = gam * f c z') ∧
      (∀ (U : (X).left.Opens) (s : Γ((X).left, U)), IsOpen {w | w ∈ (Set.univ : Set E) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U} ∧
        DifferentiableOn ℂ (fun w => valAt' (ex w).left U s) {w | w ∈ (Set.univ : Set E) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧
      (∀ c, IsAffineOpen (D c) ∧ ringKrullDim Γ(X.left, D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ f c z ≠ 0) ∧
        ∃ r : σ → Γ(X.left, D c), (∀ c' z, f c z ≠ 0 → valAt' (ex z).left (D c) (r c') = f c' z / f c z) ∧
          ∀ s : Γ(X.left, D c), ∃ F : MvPolynomial σ ℂ, s = MvPolynomial.eval₂
            (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) ∧
      (⨆ c, D c = ⊤) := by sorry
