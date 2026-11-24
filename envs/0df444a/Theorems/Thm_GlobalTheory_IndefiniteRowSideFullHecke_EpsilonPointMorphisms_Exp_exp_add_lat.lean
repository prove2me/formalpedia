-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_EpsilonPointMorphisms_Exp_exp_add_lat
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Exp.exp_add_lat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:14:32.755099+00:00
-- url     : https://prove2.me/theorems/d00f1da4-9e1a-48a1-b356-490f35f78ea5
-- title:
--   Exp: exp add lat
-- statement:
--   The Exp construction uses the exp add lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/ExponentialDifferential.lean#L83-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/ExponentialDifferential.lean#L83-L84

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Exp.exp_add_lat (z : Fin g → ℂ) (la : E.lat) : E.exp (z + la) = E.exp z := by sorry
