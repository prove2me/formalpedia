-- Prove2me | Theorems.Thm_GlobalTheory_VeryAmplePow_affine_surj
-- name    : GlobalTheory.VeryAmplePow.affine_surj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:04:25.256798+00:00
-- url     : https://prove2.me/theorems/c978deeb-a93e-4d57-8519-cb3bf5705691
-- title:
--   Very Ample Pow: affine surj
-- statement:
--   The Very Ample Pow construction uses the affine surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L35-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L35-L121

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
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
noncomputable section
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

theorem GlobalTheory.VeryAmplePow.affine_surj {Y W : Scheme.{0}} (f : Y ⟶ W) [IsAffine W] [IsProper f] [IsLocallyNoetherian W]
    (D : Y.Opens) {σ : Type} (r : σ → Γ(Y, D)) (hD : D ≤ f ⁻¹ᵁ ⊤)
    (hval : ∀ (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
      (l : Spec (.of V) ⟶ Y) (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ l) ⁻¹ᵁ D),
      (∀ j, ∃ ρ : Γ(Spec (.of V), ⊤), (Spec.map (CommRingCat.ofHom (algebraMap V K))).appTop.hom ρ =
        ((Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ l).appLE D ⊤ h).hom (r j)) → ⊤ ≤ l ⁻¹ᵁ D)
    (hmono : ∀ (Z : Scheme.{0}) [IsLocallyNoetherian Z] (x y : Z ⟶ Y) (hx : ⊤ ≤ x ⁻¹ᵁ D) (hy : ⊤ ≤ y ⁻¹ᵁ D),
      x ≫ f = y ≫ f → (∀ j, (x.appLE D ⊤ hx).hom (r j) = (y.appLE D ⊤ hy).hom (r j)) → x = y) :
    IsAffineOpen D ∧ Function.Surjective (MvPolynomial.eval₂Hom (f.appLE ⊤ D hD).hom r) := by sorry
