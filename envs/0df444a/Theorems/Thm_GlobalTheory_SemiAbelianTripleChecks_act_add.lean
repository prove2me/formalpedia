-- Prove2me | Theorems.Thm_GlobalTheory_SemiAbelianTripleChecks_act_add
-- name    : GlobalTheory.SemiAbelianTripleChecks.act_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:22:50.266449+00:00
-- url     : https://prove2.me/theorems/d7054ac0-1d8a-5ea6-b1b5-97537773b9e4
-- title:
--   Semi Abelian Triple Checks: act add
-- statement:
--   The Semi Abelian Triple Checks construction uses the act add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/CubeMapTripleProductUnique.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/CubeMapTripleProductUnique.lean#L13-L14

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_CubeMapTripleProductUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SemiAbelianTripleChecks
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}

theorem GlobalTheory.SemiAbelianTripleChecks.act_add (t : SAB H S) (a b : 𝓞 E) :
    t.act.act (a + b) = lift (t.act.act a) (t.act.act b) ≫ μ[t.G] := by sorry
