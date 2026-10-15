-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_subProg_runs
-- name    : MIPRE.Cost.Machine.subProg_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:29:38.342894+00:00
-- url     : https://prove2.me/theorems/fc7d9819-dee7-4575-8669-a56d23e04c0d
-- title:
--   Unary subtraction with comparison: `subProg` returns the flagged difference $b - a$, or $\mathsf{nil}$ if $b < a$
-- statement:
--   Natural numbers used as counters and budgets inside the self-interpreter are represented in unary: $\mathsf{ofNat}(n)$ is the list of $n$ copies of $\mathsf{nil}$ (so $\mathrm{size}(\mathsf{ofNat}\,n) = 2n + 1$). The program `subProg` is a $\mathsf{loop}$ that, on a pair of unary numerals, strips one $\mathsf{nil}$ from each until the first is exhausted or the second runs out first. Its intended value is
--   $$ \mathtt{subResult}(a, b) = \begin{cases} \mathsf{cons}\,(\mathsf{cons}\,\mathsf{nil}\,\mathsf{nil})\,\mathsf{ofNat}(b - a) & \text{if } a \le b, \\ \mathsf{nil} & \text{if } b < a, \end{cases} $$
--   a difference flagged as "defined", or the failure value $\mathsf{nil}$.
--
--   For all $a, b \in \mathbb{N}$ and every environment $\rho$, there is a cost
--   $$ t \le \mathtt{subBound}(a, b) = (a+1)(2a + 2b + 14) $$
--   such that evaluating `subProg` in the environment $\mathsf{cons}\,(\mathsf{ofNat}\,a)\,(\mathsf{ofNat}\,b) :: \rho$ halts with result $\mathtt{subResult}(a, b)$ at cost $t$.
--
--   The clocked universal machine (blueprint `lem:universal-tm`) uses this program twice per simulated step: to subtract the exact cost of the step from the remaining cost budget, where the failure value signals that the budget is exhausted, and to compare the size of the new configuration with the size guard $\Theta$.
--
--   **Formalization Note**: The program is run with the pair at variable $0$ of an environment with arbitrary further entries $\rho$ (the lemma is used inside `callVar`, which copies the argument on top of the current environment). The bound is quadratic because each of the at most $a + 1$ iterations copies both numerals, at cost proportional to $2a + 2b$; `subBound` is monotone in both arguments (`subBound_mono`), which is how it is used in the cost accounting of the clocked loop.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Universal.lean#L318-L362; internal lemma of the formalization of blueprint lem:universal-tm, https://vidick.github.io/MIPRE-formalization/blueprint/

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
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_Universal

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
open Polynomial
open MIPRE.Cost.Prog

theorem MIPRE.Cost.Machine.subProg_runs (a : ℕ) : ∀ (b : ℕ) (env : Env),
    ∃ t ≤ subBound a b,
      Eval (Data.cons (.ofNat a) (.ofNat b) :: env) subProg (subResult a b) t := by sorry
