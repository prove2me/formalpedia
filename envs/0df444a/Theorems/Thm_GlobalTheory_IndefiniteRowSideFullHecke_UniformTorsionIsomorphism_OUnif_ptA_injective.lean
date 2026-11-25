-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UniformTorsionIsomorphism_OUnif_ptA_injective
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism.OUnif.ptA_injective
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:10:48.802551+00:00
-- url     : https://prove2.me/theorems/20199485-b921-5241-b477-46ba753d915d
-- title:
--   OUnif: pt A injective
-- statement:
--   The OUnif construction uses the pt A injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/UniformTorsionIsomorphism.lean#L89-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/UniformTorsionIsomorphism.lean#L89-L90

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
open GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism.OUnif
variable {t : SAB H (Spec (CommRingCat.of R))} {Δ : OData H I} (u : OUnif t Δ)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism.OUnif.ptA_injective : Function.Injective (u.ptA F) := by sorry
