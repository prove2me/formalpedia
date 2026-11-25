-- Prove2me | Theorems.Thm_GlobalTheory_BXOf_main
-- name    : GlobalTheory.BXOf.main
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T16:50:53.696118+00:00
-- url     : https://prove2.me/theorems/0da9b62a-8e01-486b-8d8f-28071f40437b
-- title:
--   BXOf: main
-- statement:
--   The BXOf construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BiextensionSecondLawCommutativityValue.lean#L218-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BiextensionSecondLawCommutativityValue.lean#L218-L314

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BiextensionSecondLawCommutativityValue
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.BXOf
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

theorem GlobalTheory.BXOf.main :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] [IsLocalRing R₀] (g : ℕ), SmoothOfRelativeDimension g G.hom →
    ∃ (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) ∧ (∀ R x y, e R (x + y) = e R x * e R y) ∧
      (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x)) →
  (∀ {R₀ : Type} [CommRing R₀] (B₀ : BX R₀) (δ : ∀ {R S : LAlg R₀}, LHom R S → B₀.G R → B₀.G R → (S : Type)ˣ)
    (t₁ t₂ : ∀ R : LAlg R₀, B₀.G R → B₀.G R → B₀.G R → (R : Type)ˣ) (w : ∀ R : LAlg R₀, B₀.G R → B₀.G R → (R : Type)ˣ),
    (∀ R x y, δ (LHom.id R) x y = 1) →
    (∀ {Q R S : LAlg R₀} (f : LHom Q R) (h : LHom R S) x y, δ (h.comp f) x y = Units.map (h.1 : (R : Type) →* (S : Type)) (δ f x y) * δ h (B₀.map f x) (B₀.map f y)) →
    (∀ R x x' x'' y, t₁ R (x + x') x'' y * t₁ R x x' y = t₁ R x (x' + x'') y * t₁ R x' x'' y) → (∀ R x x' y, t₁ R x x' y = t₁ R x' x y) →
    (∀ R x y y' y'', t₂ R x (y + y') y'' * t₂ R x y y' = t₂ R x y (y' + y'') * t₂ R x y' y'') → (∀ R x y y', t₂ R x y y' = t₂ R x y' y) →
    (∀ R x x' y y', t₁ R x x' (y + y') * t₂ R x y y' * t₂ R x' y y' = t₂ R (x + x') y y' * t₁ R x x' y * t₁ R x x' y') →
    (∀ {R S : LAlg R₀} (f : LHom R S) x x' y, Units.map (f.1 : (R : Type) →* (S : Type)) (t₁ R x x' y) * δ f (x + x') y =
      δ f x y * δ f x' y * t₁ S (B₀.map f x) (B₀.map f x') (B₀.map f y)) →
    (∀ {R S : LAlg R₀} (f : LHom R S) x y y', Units.map (f.1 : (R : Type) →* (S : Type)) (t₂ R x y y') * δ f x (y + y') =
      δ f x y * δ f x y' * t₂ S (B₀.map f x) (B₀.map f y) (B₀.map f y')) →
    (∀ R x y, w R x y * w R y x = 1) → (∀ R x x' y, t₁ R x x' y * w R (x + x') y = w R x y * w R x' y * t₂ R y x x') →
    (∀ {R S : LAlg R₀} (f : LHom R S) x y, Units.map (f.1 : (R : Type) →* (S : Type)) (w R x y) * δ f y x = δ f x y * w S (B₀.map f x) (B₀.map f y)) →
    ∃ (B : BX R₀) (κ : ∀ R, B.G R ≃+ B₀.G R) (b : ∀ R x y, B.P R x y),
      (∀ {R S : LAlg R₀} (f : LHom R S) x, κ S (B.map f x) = B₀.map f (κ R x)) ∧
      (∀ R x x' y, B.add1 (b R x y) (b R x' y) = B.smul (t₁ R (κ R x) (κ R x') (κ R y)) (b R (x + x') y)) ∧
      (∀ R x y y', B.add2 (b R x y) (b R x y') = B.smul (t₂ R (κ R x) (κ R y) (κ R y')) (b R x (y + y'))) ∧
      (∀ {R S : LAlg R₀} (f : LHom R S) x y, B.pmap f (b R x y) = B.smul (δ f (κ R x) (κ R y)) (b S (B.map f x) (B.map f y)))) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] [IsLocalRing R₀] (g : ℕ), SmoothOfRelativeDimension g G.hom →
    ∀ (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (s : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb P (K := Fin 2) ![(lift (snd G G) (fst G G)).left, 𝟙 (G ⊗ G).left] ![1, -1])),
    (s.IsGen ∧ ∀ (T : Over (Spec (CommRingCat.of R₀))) (z : T.left) (J : (T.left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J → ∀ x x' y : T ⟶ G,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift x y).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift y x).left z J = 1 ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift x (lift x' y)).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift (x * x') y).left z J =
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift x y).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift x' y).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift y (lift x x')).left z J) →
    ∃ (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) ∧ (∀ R x y, e R (x + y) = e R x * e R y) ∧
      (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) ∧
      ∃ (b : ∀ R x y, B.P R x y) (J : ∀ R : LAlg R₀, ((sp (R₀ := R₀) (R : Type)).left ⟶ (G ⊗ G).left) → P.1),
        (∀ R : LAlg R₀, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P (Z := (sp (R₀ := R₀) (R : Type)).left) (IsLocalRing.closedPoint (R : Type)) (J R)) ∧
        (∀ (R : LAlg R₀) x x' y, B.add1 (b R x y) (b R x' y) =
          B.smul (Units.map (stalkClosedPointIso (CommRingCat.of (R : Type))).hom.hom.toMonoidHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift (e R x) (lift (e R x') (e R y))).left (IsLocalRing.closedPoint (R : Type)) (J R))) (b R (x + x') y)) ∧
        (∀ (R : LAlg R₀) x y y', B.add2 (b R x y) (b R x y') =
          B.smul (Units.map (stalkClosedPointIso (CommRingCat.of (R : Type))).hom.hom.toMonoidHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift (e R x) (lift (e R y) (e R y'))).left (IsLocalRing.closedPoint (R : Type)) (J R))) (b R x (y + y')))) := by sorry
