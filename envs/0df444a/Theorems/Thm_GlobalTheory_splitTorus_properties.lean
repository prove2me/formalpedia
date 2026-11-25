-- Prove2me | Theorems.Thm_GlobalTheory_splitTorus_properties
-- name    : GlobalTheory.splitTorus_properties
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:15:33.44657+00:00
-- url     : https://prove2.me/theorems/03763ad4-5d9a-5985-aa47-1499043d57ee
-- title:
--   Global Theory: split Torus properties
-- statement:
--   The Global Theory construction uses the split Torus properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentationDiagMap.lean#L605-L656
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentationDiagMap.lean#L605-L656

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open GlobalTheory
open Diag

theorem GlobalTheory.splitTorus_properties (S : Scheme.{0}) :
    (∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X],
      IsAffineHom (splitTorus S X).hom ∧ LocallyOfFinitePresentation (splitTorus S X).hom ∧
      QuasiCompact (splitTorus S X).hom ∧ QuasiSeparated (splitTorus S X).hom ∧
      SmoothOfRelativeDimension (Module.finrank ℤ X) (splitTorus S X).hom ∧
      Surjective (splitTorus S X).hom ∧ GeometricallyIntegral (splitTorus S X).hom ∧
      GeometricallyConnected (splitTorus S X).hom ∧ IsSemiAbelian (splitTorus S X) ∧
      (Nonempty S → Nontrivial X → 𝟙 (splitTorus S X) ≠ 1) ∧
      ∀ n : ℕ, 1 ≤ n → IsFinite (mulN (splitTorus S X) n).left ∧
        Flat (mulN (splitTorus S X) n).left ∧ Surjective (mulN (splitTorus S X) n).left ∧
        LocallyOfFinitePresentation (mulN (splitTorus S X) n).left ∧
        ∀ y, (mulN (splitTorus S X) n).left.finrank y = n ^ Module.finrank ℤ X) ∧
    (∀ (S' : Scheme.{0}) (f : S' ⟶ S) (X : Type) [AddCommGroup X],
      IsMonHom (baseChangeIso f X : (Over.pullback f).obj (splitTorus S X) ≅ splitTorus S' X).hom ∧
      ∀ (Y : Type) [AddCommGroup Y] (u : Y →+ X),
        (Over.pullback f).map (diagMap S u) ≫ (baseChangeIso f Y).hom =
          (baseChangeIso f X).hom ≫ diagMap S' u) ∧
    (∀ (X : Type) [AddCommGroup X] [Finite X],
      IsFinite (splitTorus S X).hom ∧ Flat (splitTorus S X).hom ∧
      LocallyOfFinitePresentation (splitTorus S X).hom ∧
      (∀ s, (splitTorus S X).hom.finrank s = Nat.card X) ∧
      (IsUnit (Nat.card X : Γ(S, ⊤)) → Etale (splitTorus S X).hom)) ∧
    (∀ (X Y : Type) [AddCommGroup X] [AddCommGroup Y] (u : Y →+ X),
      IsMonHom (diagMap S u : splitTorus S X ⟶ splitTorus S Y) ∧
      (∀ y, (diagMap S u).left.appTop.hom (chi Y y) = chi X (u y)) ∧
      (∀ v : Y →+ X, diagMap S (u + v) = diagMap S u * diagMap S v) ∧
      (∀ (Z : Type) [AddCommGroup Z] (v : Z →+ Y), diagMap S (u.comp v) = diagMap S u ≫ diagMap S v) ∧
      IsPullback (diagMap S (QuotientAddGroup.mk' u.range)) (toUnit _) (diagMap S u)
        (η : 𝟙_ (Over S) ⟶ splitTorus S Y) ∧
      (Function.Surjective u → IsClosedImmersion (diagMap S u).left) ∧
      (Function.Injective u → Flat (diagMap S u).left ∧ Surjective (diagMap S u).left) ∧
      (u.range.FiniteIndex → IsFinite (diagMap S u).left) ∧
      (Function.Injective u → u.range.FiniteIndex →
        LocallyOfFinitePresentation (diagMap S u).left ∧
          ∀ y, (diagMap S u).left.finrank y = u.range.index)) ∧
    (∀ (X : Type) [AddCommGroup X] (n : ℕ),
      diagMap S (AddMonoidHom.id X) = 𝟙 (splitTorus S X) ∧
      mulN (splitTorus S X) n = diagMap S (nsmulAddMonoidHom n) ∧
      ∃ e : torsion (splitTorus S X) n ≅ splitTorus S (X ⧸ (nsmulAddMonoidHom n : X →+ X).range),
        e.hom ≫ diagMap S (QuotientAddGroup.mk' _) = torsion.ι (splitTorus S X) n) := by sorry
