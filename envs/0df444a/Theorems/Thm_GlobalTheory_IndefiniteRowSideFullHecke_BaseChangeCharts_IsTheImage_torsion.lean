-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_BaseChangeCharts_IsTheImage_torsion
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeCharts.IsTheImage.torsion
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:10:17.051522+00:00
-- url     : https://prove2.me/theorems/5ee88824-f9be-5457-b58f-472dec56383c
-- title:
--   Is The Image: torsion
-- statement:
--   The Is The Image construction uses the torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/BaseChangeCharts.lean#L149-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/BaseChangeCharts.lean#L149-L152

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtPtBridgeSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_BaseChangeCharts
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
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeCharts
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeCharts.IsTheImage.torsion {U : Unif I D A G} {k : ℕ} {p : QkPt D.toPre F k}
    {x : TFK (R := R) F ⟶ A.A} (h : IsTheImage F U k p x) : x ^ k = 1 := by sorry
