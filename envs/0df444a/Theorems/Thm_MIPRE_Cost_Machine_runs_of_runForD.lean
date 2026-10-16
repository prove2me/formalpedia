-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_runs_of_runForD
-- name    : MIPRE.Cost.Machine.runs_of_runForD
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:25:34.670289+00:00
-- url     : https://prove2.me/theorems/23953d5b-bfd2-43d1-9189-5f2e9f9795d4
-- title:
--   Soundness of the budgeted evaluator: whatever it returns is a genuine run
-- statement:
--   The ambient cost model has programs `Prog` (de Bruijn variables, `nil`, constants, `cons`, `elim`, `let_` and `loop`) acting on binary trees `Data`, with a timed big-step semantics `Eval env p r t`: in the environment `env`, $p$ halts with result $r$ at cost $t$. `p.Runs x r t` is `Eval [x] p r t`, the run of $p$ on the single input $x$. `Machine.runForD pd x k` is the computable budgeted evaluator: from the datum `pd` encoding a program and the input $x$, it iterates the machine's step function $3k$ times from the initial configuration and returns `some` of the result if the configuration reached is final, and `none` otherwise. Let $p$ be a program, $x$ and $r$ data and $k$ a natural number, and assume `runForD (encode p) x k = some r`. Then
--
--   $$\exists\, t \in \mathbb{N},\qquad p.\mathrm{Runs}\ x\ r\ t .$$
--
--   This is one of the two directions of the correctness of the budgeted evaluator; with its converse `runForD_eq_some` (a run of cost at most $k$ is found) it gives `runForD_eq_some_iff`, the decision procedure that lets the tabulations of verifier games fill in their acceptance tables by budgeted runs.
--
--   **Formalization Note** No bound on the cost $t$ is asserted; the conclusion is existential in the cost. `encode p` is `Prog.toData p`, the program as data. The budget $3k$ and the step function are internal to `runForD`; the hypothesis is an equation between values of type `Option Data`. The arguments `p`, `x`, `r`, `k` are implicit and the proposition is `MIPRE.Cost.Machine.runs_of_runForD`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/BoundedEval.lean#L76-L89

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine

theorem MIPRE.Cost.Machine.runs_of_runForD {p : Prog} {x r : Data} {k : ℕ} (h : runForD (encode p) x k = some r) :
    ∃ t, p.Runs x r t := by sorry
