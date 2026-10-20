-- Prove2me | Theorems.Thm_OAI_SingleFold_Counter_eval_dom_iff_halts
-- name    : OAI.SingleFold.Counter.eval_dom_iff_halts
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:49:27.328121+00:00
-- url     : https://prove2.me/theorems/215498dc-3a99-47e0-b7a2-487b8925e54c
-- title:
--   Evaluation of a counter machine terminates iff it halts
-- statement:
--   For a counter machine $M$ and input $d$, let $\mathrm{step}$ return the next configuration, or nothing in the halting state, and let $\mathrm{eval}$ iterate $\mathrm{step}$ from the start configuration as a partial value. Then
--   $$
--   \mathrm{eval}(\mathrm{step},\langle\mathrm{start},d\rangle)\ \text{is defined}\iff M\text{ halts on }d .
--   $$
--
--   This connects the step-function semantics used to simulate Mathlib's machines with the halting predicate used by the arithmetization.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/MacroMachine.lean#L386-L398

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterMachine
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterBounds
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterCompilation
import Definitions.Def_OAI_NumberTheory_SingleFold_MacroMachine

open OAI OAI.SingleFold OAI.SingleFold.Counter
open StateTransition Relation
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]

theorem OAI.SingleFold.Counter.eval_dom_iff_halts (M : Machine Q J) (d : J → ℕ) :
    (eval (step M) ⟨M.start,d⟩).Dom ↔ Halts M d := by sorry
