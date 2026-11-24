-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UniformTorsionIsomorphism_toGen_injective
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism.toGen_injective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:16:11.597809+00:00
-- url     : https://prove2.me/theorems/a4c62c7b-c5b1-42ed-9382-ab911bc42bff
-- title:
--   Uniform Torsion Isomorphism: to Gen injective
-- statement:
--   The Uniform Torsion Isomorphism construction uses the to Gen injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/UniformTorsionIsomorphism.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/UniformTorsionIsomorphism.lean#L75-L78

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegOUnif
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TorusGraphMaps
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_UniformTorsionIsomorphism
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps
open scoped CategoryTheory.Obj
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {R : Type} [CommRing R] [IsDomain R]
attribute [instance] OData.mod
variable {H : Host E} {I : Ideal R}
variable {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism.toGen_injective {G : Over (Spec (CommRingCat.of R))} :
    Function.Injective (toGen (R := R) (F := F) (G := G)) := by sorry
