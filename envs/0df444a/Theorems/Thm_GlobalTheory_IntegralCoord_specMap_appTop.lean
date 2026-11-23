-- Prove2me | Theorems.Thm_GlobalTheory_IntegralCoord_specMap_appTop
-- name    : GlobalTheory.IntegralCoord.specMap_appTop
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:20:15.928447+00:00
-- url     : https://prove2.me/theorems/9d2cb51c-c638-4f84-a0a1-b2d7a82f5864
-- title:
--   Integral Coord: spec Map app Top
-- statement:
--   The Integral Coord construction uses the spec Map app Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsBasisOfEq.lean#L55-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsBasisOfEq.lean#L55-L62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsBasisOfEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IntegralCoord
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

theorem GlobalTheory.IntegralCoord.specMap_appTop {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (c : Γ(Spec (CommRingCat.of A), ⊤)) :
    (Spec.map (CommRingCat.ofHom f)).appTop.hom c =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom c)) := by sorry
