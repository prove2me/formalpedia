-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_stepProg_runs
-- name    : MIPRE.Cost.Machine.stepProg_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:28:20.774552+00:00
-- url     : https://prove2.me/theorems/9a9db460-daf8-4813-b809-cfb7dbaac8a2
-- title:
--   The step program of the self-interpreter computes one machine step within cost $(S+1)(S+40)+200$
-- statement:
--   We work in the ambient cost model of the formalization: data are binary trees (`Data`, from `nil` and `cons`), $\mathrm{size}(d)$ is the number of nodes of $d$, and $\mathrm{Eval}(\mathrm{env}, p, r, t)$ is the timed semantics (the program $p$ in the environment $\mathrm{env}$ halts with $r$ at cost exactly $t$; one unit per rule, plus the size of every value read by a variable or literal). The self-interpreter implements, as a program, the step function of a small-step evaluation machine whose configurations are encoded as data: an environment is a `cons`-chain of values, a stack a `cons`-chain of encoded frames, and a program $p$ is its tree encoding $\mathrm{toData}(p)$, a unary tag ($0$ to $6$ for `var`, `nil`, `cons`, `elim`, `let_`, `loop`, `const`) paired with the fields.
--
--   A configuration $c = \langle \mathrm{ctrl}, \mathrm{env}, \mathrm{kont}\rangle$ of the evaluation machine consists of a control (either "evaluate $p$" or "return $v$"), an environment (a list of values) and a stack of frames; its encoding is $\mathrm{toData}(c) = \texttt{cons}(\mathrm{toData}(\mathrm{ctrl}), \texttt{cons}(\mathrm{list}(\mathrm{env}), \mathrm{list}(\mathrm{kont})))$, with $\mathrm{toData}(\text{evaluate } p) = \texttt{cons}(\texttt{nil}, \mathrm{toData}(p))$ and $\mathrm{toData}(\text{return } v) = \texttt{cons}(\texttt{cons}(\texttt{nil},\texttt{nil}), v)$. The machine's step function $\mathrm{step}$ performs one evaluation rule (final configurations, a returned value with an empty stack, are fixed points), and is set up so that the costs charged along a run add up exactly to the cost of the corresponding derivation in the timed semantics.
--
--   Let $c$ be any configuration and $S = \mathrm{size}(\mathrm{toData}(c))$. Then there is a cost $s$ with
--
--   $$ s \le (S+1)(S+40) + 200 \quad\text{and}\quad \texttt{stepProg}\ \text{on the input}\ \mathrm{toData}(c)\ \text{halts with}\ \mathrm{toData}(\mathrm{step}(c))\ \text{at cost}\ s. $$
--
--   This is the step of the self-interpreter of the ambient language written in the language itself. The universal program `univProg` iterates `stepProg` from the initial configuration of a program on its input until a final configuration is reached, and the clocked variant `univTProg` does so under a budget; since every configuration along a run of cost $t$ has size polynomial in the sizes of the program and input and in $t$, the quadratic cost per step yields the polynomial overhead of the efficient universal machine (blueprint `lem:universal-tm`) and of its clocked form.
--
--   **Formalization Note**. The bound is `stepBound S = (S + 1) * (S + 40) + 200` of `MIPRE.Cost.Machine`, and the conclusion is `stepProg.Runs c.toData (step c).toData s` with `step` the machine's step on `Cfg` and `Cfg.toData` the encoding of `Cost/MachineData.lean`. The proof goes through the data-level step `stepData`, which agrees with the machine on encoded configurations (`stepData_toData`), and through the two half-step programs `stepEvProg` and `stepRetProg`, whose quadratic and linear bounds are absorbed into `stepBound` by the two auxiliary inequalities `le_stepBound_of_quad` and `le_stepBound_of_le`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Interpreter.lean#L835-L905; internal lemma of the formalization of blueprint lem:universal-tm (the step program of the self-interpreter)

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
open MIPRE.Cost.Prog

theorem MIPRE.Cost.Machine.stepProg_runs (c : Cfg) :
    ∃ s ≤ stepBound (Cfg.toData c).size, stepProg.Runs c.toData (step c).toData s := by sorry
