-- Prove2me | Theorems.Thm_GlobalTheory_ModelScope_extends_of_not_subset
-- name    : GlobalTheory.ModelScope.extends_of_not_subset
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:27:20.816902+00:00
-- url     : https://prove2.me/theorems/576f45d9-bf90-4e5c-b0c8-5ea57a1b2172
-- title:
--   Model Scope: extends of not subset
-- statement:
--   The Model Scope construction uses the extends of not subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/RangeJSubsetAbLocus.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/RangeJSubsetAbLocus.lean#L14-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_RangeJSubsetAbLocus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ModelScope
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem GlobalTheory.ModelScope.extends_of_not_subset (Y : Model Xo c β) (U : Y.X.Opens) (hU : ¬ Set.range Y.j ⊆ (U : Set Y.X))
    (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) : Y.Extends U σ := by sorry
