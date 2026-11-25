-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_EpsilonPointMorphisms_Exp_exp_zero
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Exp.exp_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:42.760528+00:00
-- url     : https://prove2.me/theorems/357657ee-2365-5c8d-9d60-ee3ef0c456e6
-- title:
--   Exp: exp zero
-- statement:
--   The Exp construction uses the exp zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/ExponentialDifferential.lean#L73-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/ExponentialDifferential.lean#L73-L73

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_ExponentialDifferential
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms
open GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Exp
variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} (E : Exp A g)

theorem GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Exp.exp_zero : E.exp 0 = 1 := by sorry
