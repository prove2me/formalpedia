-- Prove2me | Theorems.Thm_GlobalTheory_gm_div_pull_g
-- name    : GlobalTheory.gm_div_pull_g
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:14:43.566693+00:00
-- url     : https://prove2.me/theorems/980b7af3-7863-5c2d-ba05-3b217ece736a
-- title:
--   Global Theory: gm div pull g
-- statement:
--   The Global Theory construction uses the gm div pull g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L236-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L236-L244

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
variable {I : Type} [SmallCategory I] [IsCofiltered I]
variable (D : I ⥤ Scheme.{0}) {X : Scheme.{0}} (π : ∀ i, X ⟶ D.obj i)
  (w : ∀ {i j} (f : i ⟶ j), π i ≫ D.map f = π j) (hc : IsLimit (schemeConeOfFamily D π w))
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

theorem GlobalTheory.gm_div_pull_g {Y Z : Scheme.{0}} (M N : LB Y) (F : Z ⟶ Y) (z : Z) (p q : N.ι × M.ι)
    (hz : F z ∈ (LB.div N M).U p ⊓ (LB.div N M).U q) :
    gm (𝟙 Z) z _ ((LB.div (N.pull F) (M.pull F)).g (fun _ => p.1, fun _ => p.2) (fun _ => q.1, fun _ => q.2)) =
      gm F z _ ((LB.div N M).g p q) := by sorry
