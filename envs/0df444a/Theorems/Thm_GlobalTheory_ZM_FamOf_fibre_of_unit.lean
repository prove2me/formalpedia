-- Prove2me | Theorems.Thm_GlobalTheory_ZM_FamOf_fibre_of_unit
-- name    : GlobalTheory.ZM.FamOf.fibre_of_unit
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:00:06.972871+00:00
-- url     : https://prove2.me/theorems/484b6f46-815d-46bd-b6ad-1f2881436391
-- title:
--   Fam Of: fibre of unit
-- statement:
--   The Fam Of construction uses the fibre of unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSectionsFam.lean#L76-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSectionsFam.lean#L76-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DenseOfDenseP
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSectionsFam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.FamOf

theorem GlobalTheory.ZM.FamOf.fibre_of_unit {R K σ : Type} [CommRing R] [CommRing K] {x : R →+* K} {Z : Scheme.{0}} {s : Z ⟶ Sp R} {M : LB Z}
    {th : σ → M.Sec} (A : Over (Sp K)) (L : LB A.left) (k : ℕ) (a : ℤ) (ha : a = k)
    (th' : σ → (Out.LPow A L a (Over.mk (𝟙 (Sp K)))).Sec) (φ₀ : (Over.mk (𝟙 (Sp K)) ⊗ A).left ⟶ Z)
    (h1 : IsPullback φ₀ (fst (Over.mk (𝟙 (Sp K))) A).left s (spMap x))
    (h2 : LBIso (Out.LPow A L a (Over.mk (𝟙 (Sp K)))) (M.pull φ₀))
    (h3 : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ A).left) (w : σ → T),
      SecCoord _ th' y w ↔ SecCoord M th (y ≫ φ₀) w) :
    ∃ φ : A.left ⟶ Z, IsPullback φ A.hom s (spMap x) ∧
      (∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ A).left) (w : σ → T),
        SecCoord _ th' y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) A).left ≫ φ) w) ∧
      LBIso (lbPow L k) (M.pull φ) ∧
      ∀ (z : Over.mk (𝟙 (Sp K)) ⟶ A) (w : σ → K), SecCoord _ th' (lift (𝟙 (Over.mk (𝟙 (Sp K)))) z).left w →
        SecCoord M th (z.left ≫ φ) w := by sorry
