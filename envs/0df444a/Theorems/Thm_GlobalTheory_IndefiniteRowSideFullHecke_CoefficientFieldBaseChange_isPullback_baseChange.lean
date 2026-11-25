-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CoefficientFieldBaseChange_isPullback_baseChange
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.isPullback_baseChange
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:40.352777+00:00
-- url     : https://prove2.me/theorems/80be8980-894a-49f7-a327-9eb22b04beee
-- title:
--   Coefficient Field Base Change: is Pullback base Change
-- statement:
--   The Coefficient Field Base Change construction uses the is Pullback base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/CoefficientFieldBaseChange.lean#L102-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/CoefficientFieldBaseChange.lean#L102-L104

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoefficientFieldBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CoefficientFieldBaseChange
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem GlobalTheory.IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.isPullback_baseChange {l : Level H} {X : Scheme.{0}} (str : X ⟶ Sp (KA l)) {F₀ : IntermediateField ℚ ℂ}
    (h : IsCoeffField l F₀) : IsPullback (baseChangeFst str h) (baseChangeStr str h) str (spMap h.incl) := by sorry
