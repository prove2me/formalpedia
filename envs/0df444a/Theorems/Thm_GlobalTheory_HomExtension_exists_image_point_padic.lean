-- Prove2me | Theorems.Thm_GlobalTheory_HomExtension_exists_image_point_padic
-- name    : GlobalTheory.HomExtension.exists_image_point_padic
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:19:35.705339+00:00
-- url     : https://prove2.me/theorems/f4dc32ec-9f78-46e9-98eb-083acaafca0c
-- title:
--   Hom Extension: exists image point padic
-- statement:
--   The Hom Extension construction uses the exists image point padic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteResidueFieldIntegralClosurePadicInt.lean#L142-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteResidueFieldIntegralClosurePadicInt.lean#L142-L203

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulEquivOfIsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SemiAbelianTorsionFiniteAndClosedPointFiniteOrde
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldIntegralClosurePadicInt
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory
open GlobalTheory.HomExtension

theorem GlobalTheory.HomExtension.exists_image_point_padic
    (hext : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
      [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'],
      IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶
        (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f →
        ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)
    {Z U : Scheme.{0}} (π : Z ⟶ Sp ℤ) [LocallyOfFiniteType π] (j : U ⟶ Z) [IsOpenImmersion j]
    {G G' : Over Z} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G)
    (hG' : IsSemiAbelian G') (φ : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G') [IsMonHom φ]
    (p : ℕ) [Fact p.Prime] (a : Sp (OO p) ⟶ G.left) (a₀ : Sp (PadicAlgCl p) ⟶ pullback G.hom j)
    (ha : a₀ ≫ pullback.fst G.hom j = gPt p ≫ a) (n : ℕ)
    (hn : ∀ (K : Type) [Field K] (t : Sp K ⟶ Z) (x : Over.mk t ⟶ G),
      Set.range x.left = {a (cPt p)} → x ^ n = 1) :
    ∃ b : Sp (OO p) ⟶ G'.left, b ≫ G'.hom = a ≫ G.hom ∧
      gPt p ≫ b = a₀ ≫ φ.left ≫ pullback.fst G'.hom j ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (t : Sp k ⟶ Z) (x : Over.mk t ⟶ G'),
        x ^ n = 1 ∧ b (cPt p) ∈ Set.range x.left := by sorry
