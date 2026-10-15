-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_clockBody_prefix
-- name    : MIPRE.Cost.Machine.clockBody_prefix
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:29:51.329927+00:00
-- url     : https://prove2.me/theorems/38859d7f-8668-4896-b637-bfffaefc1a0d
-- title:
--   One iteration of the clocked loop, first half: finality test, step cost and budget subtraction
-- statement:
--   The clocked self-interpreter runs the evaluation machine under a cost budget. Its loop state is $\mathtt{clockState}(d, \mathit{rem}, \mathit{bud}, \theta) = \mathsf{cons}\,d\,(\mathsf{cons}\,\mathit{rem}\,(\mathsf{cons}\,\mathit{bud}\,\theta))$: the encoded configuration $d$, the remaining cost budget, the remaining step budget and the size guard, the last three as unary numerals. The loop body `clockBody` tests whether the configuration is final and otherwise, if the step budget is positive, computes the cost of the next step with `stepCostProg`, subtracts it from the remaining cost budget with the unary subtraction `subProg`, and then runs the second half `clockRest` (perform the step, compare the new configuration's size with the guard, and continue or stop). Let $\mathtt{clockEnv}(c, \mathit{rem}, b, \Theta, \rho)$ denote the environment reached at that point: on top of the loop state and the intermediate values it holds the pair $(\mathsf{ofNat}(\mathsf{stepCost}\,c), \mathsf{ofNat}\,\mathit{rem})$ and, at variable $0$, the value $\mathtt{subResult}(\mathsf{stepCost}\,c, \mathit{rem})$ of the subtraction (the flagged difference, or $\mathsf{nil}$ when the step cost exceeds the remaining budget).
--
--   Let $c$ be a configuration that is not final, let $\mathit{rem}, b, \Theta \in \mathbb{N}$, let $\rho$ be an environment, $r$ a value and $t \in \mathbb{N}$. Suppose that the remainder of the body, the program $\mathsf{elim}\,0\,(\mathsf{cons}\,\mathsf{nil}\,\mathsf{nil})\,\mathtt{clockRest}$ which stops with $\mathsf{nil}$ if the subtraction failed and otherwise runs `clockRest`, halts in the environment $\mathtt{clockEnv}(c, \mathit{rem}, b, \Theta, \rho)$ with result $r$ at cost $t$. Then there is a cost
--   $$ s \le t + \mathtt{stepCostBound}\bigl(\mathrm{size}\lceil c\rceil\bigr) + \mathtt{subBound}\bigl(\mathsf{stepCost}(c), \mathit{rem}\bigr) + 4\,\mathrm{size}\lceil c\rceil + 4\,\mathit{rem} + 30 $$
--   such that `clockBody` halts in the environment $\mathtt{clockState}(\lceil c\rceil, \mathsf{ofNat}\,\mathit{rem}, \mathsf{ofNat}(b+1), \mathsf{ofNat}\,\Theta) :: \rho$ with the same result $r$ at cost $s$. Here $\mathtt{stepCostBound}(S) = (S+1)(7S+32) + 13S + 50$ and $\mathtt{subBound}(a, b) = (a+1)(2a+2b+14)$.
--
--   The lemma is the common prefix of the three outcomes of a non-final iteration with positive step budget in the correctness proof of the clocked loop (`clockLoop_runs`): continue with the stepped configuration, stop because the guard is exceeded, or stop because the step cost exceeds the remaining budget. It serves the clocked universal machine of blueprint `lem:universal-tm`.
--
--   **Formalization Note**: The step budget is written $b + 1$ because the body's first action on a non-final configuration is to test it against $\mathsf{nil}$ (the exhausted-budget case is `clockBody_budget0`). `clockEnv` is the explicit twelve-entry environment of `Cost/Universal.lean`; the statement is a cost transfer from the second half to the whole body, with $r$ and the hypothesis run arbitrary.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Universal.lean#L898-L926; internal lemma of the formalization of blueprint lem:universal-tm, https://vidick.github.io/MIPRE-formalization/blueprint/

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

theorem MIPRE.Cost.Machine.clockBody_prefix (c : Cfg) (hc : ¬ IsFinal c) (rem b Θ : ℕ) (env : Env) (r : Data)
    {t : ℕ} (hrest : Eval (clockEnv c rem b Θ env) (.elim 0 (.cons .nil .nil) clockRest) r t) :
    ∃ s ≤ t + stepCostBound (Cfg.toData c).size + subBound (stepCost c) rem +
        4 * (Cfg.toData c).size + 4 * rem + 30,
      Eval (clockState c.toData (.ofNat rem) (.ofNat (b + 1)) (.ofNat Θ) :: env) clockBody r s := by sorry
