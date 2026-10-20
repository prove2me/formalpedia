-- Prove2me | Theorems.Thm_OAI_SingleFold_TM2Macro_stepAux_reaches
-- name    : OAI.SingleFold.TM2Macro.stepAux_reaches
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:50:49.289299+00:00
-- url     : https://prove2.me/theorems/2877a5fd-fe7e-4799-b643-c3aa36138a38
-- title:
--   The macro program simulates one stack-machine statement
-- statement:
--   Consider Mathlib's stack machine for partial recursive functions, with stacks packed in base $5$ as $\mathrm{pack}(s::l)=5\,\mathrm{pack}(l)+\mathrm{digit}(s)$, and its simulating macro program. For every statement $q$, store value $v$, stack contents $S$ and extra registers $x$, the macro program reaches, in at least one step, from the configuration labelled $(q,v)$ with registers $(\mathrm{pack}\circ S,x)$ the encoding of
--   $$
--   \mathrm{stepAux}(q,v,S),
--   $$
--   the stack-machine configuration after executing $q$.
--
--   Each statement of the stack machine is executed faithfully by a short sequence of macro instructions, and the simulation stays exact on the packed stacks.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/TuringSimulation.lean#L92-L142

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
import Definitions.Def_OAI_NumberTheory_SingleFold_TuringSimulation

open OAI OAI.SingleFold OAI.SingleFold.TM2Macro
open Turing Turing.PartrecToTM2 StateTransition Relation
open Macro (mod5)
variable {n : ℕ} {Λ : Type}

theorem OAI.SingleFold.TM2Macro.stepAux_reaches (M : Λ → Stmt Λ) (initial : Λ) (q : Stmt Λ) (v : Store)
    (S : Stack → List Symbol) (x : Fin n → ℕ) :
    Reaches₁ (Macro.step (program M initial)) (codeCfg q v S x) (encode M (TM2.stepAux q v S) x) := by sorry
