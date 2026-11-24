-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGroupTest_weilIs_unique_of_local
-- name    : GlobalTheory.ThetaGroupTest.weilIs_unique_of_local
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:06:43.325059+00:00
-- url     : https://prove2.me/theorems/0cb962e1-750d-42b6-a7a4-e13fed9caac4
-- title:
--   Theta Group Test: weil Is unique of local
-- statement:
--   The Theta Group Test construction uses the weil Is unique of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AbelianLawCounterexamples/WeilIsUniqueOfLocal.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AbelianLawCounterexamples/WeilIsUniqueOfLocal.lean#L33-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_WeilIsUniqueOfLocal
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaGroupTest
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
  ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits GlobalTheory.ThetaScalar
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}

theorem GlobalTheory.ThetaGroupTest.weilIs_unique_of_local (p : T.left) (hp : ∀ V : T.left.Opens, p ∈ V → V = ⊤) (hL : L.IsLB) {x y : T ⟶ A}
    {c c' : Γ(T.left, ⊤)ˣ} (h : WeilIs A L k x y c) (h' : WeilIs A L k x y c') :
    unitRes (T := T) ⊤ c = unitRes (T := T) ⊤ c' := by sorry
