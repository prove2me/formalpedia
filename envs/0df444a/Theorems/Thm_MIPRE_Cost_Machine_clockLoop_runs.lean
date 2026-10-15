-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_clockLoop_runs
-- name    : MIPRE.Cost.Machine.clockLoop_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:29:45.115605+00:00
-- url     : https://prove2.me/theorems/5b8ce2c6-e9f2-41bd-9b94-e87b0de8ef51
-- title:
--   The clocked loop computes `clockRun` at cost $(b+1)(\mathtt{clockBodyBound}(\Theta,k)+1)$ for step budget $b$
-- statement:
--   The clocked self-interpreter runs the evaluation machine from a configuration $c_0$ under three guards: a cost budget $k$ (the cumulative cost $\mathsf{costSum}(c_0, n)$ of the first $n$ steps, which is the sum of the charges $\mathsf{stepCost}$ along the run, may not exceed $k$), a step budget $b$ (at most $b$ further iterations), and a size guard $\Theta$ (the encoded size of every configuration handled may not exceed $\Theta$). Its loop state is $\mathtt{clockState}(\lceil c\rceil, \mathsf{ofNat}\,\mathit{rem}, \mathsf{ofNat}\,b, \mathsf{ofNat}\,\Theta)$, where $\mathit{rem}$ is the remaining cost budget, and the body `clockBody` stops with the flagged value $\mathsf{cons}\,(\mathsf{cons}\,\mathsf{nil}\,\mathsf{nil})\,r$ on a final configuration with value $r$, stops with $\mathsf{nil}$ when the step budget is exhausted, when the next step costs more than the remaining budget, or when the next configuration exceeds the guard, and otherwise continues with the stepped configuration, the decremented budgets and the same guard.
--
--   The intended value of the loop is the function $\mathtt{clockRun}(c_0, k, \Theta, b, n)$, defined by recursion on $b$: if the $n$-th configuration $\mathsf{step}^{n}(c_0)$ is final it is the flagged value of that configuration; otherwise, if $b = 0$ it is $\mathsf{nil}$, and if $b = b' + 1$ it is $\mathtt{clockRun}(c_0, k, \Theta, b', n+1)$ when $\mathsf{costSum}(c_0, n+1) \le k$ and $\mathrm{size}\lceil\mathsf{step}^{n+1}(c_0)\rceil \le \Theta$, and $\mathsf{nil}$ otherwise.
--
--   Let $c_0$ be a configuration, $k, \Theta \in \mathbb{N}$ and $\rho$ an environment. For all $b, n \in \mathbb{N}$ such that
--   1. $b \le 3k + 1$,
--   2. $\mathsf{costSum}(c_0, n) \le k$, and
--   3. $\mathrm{size}\lceil\mathsf{step}^{n}(c_0)\rceil \le \Theta$,
--
--   there is a cost
--   $$ t \le (b+1)\bigl(\mathtt{clockBodyBound}(\Theta, k) + 1\bigr) $$
--   such that $\mathsf{loop}\;\mathtt{clockBody}$, evaluated in the environment $\mathtt{clockState}\bigl(\lceil\mathsf{step}^{n}(c_0)\rceil, \mathsf{ofNat}(k - \mathsf{costSum}(c_0, n)), \mathsf{ofNat}\,b, \mathsf{ofNat}\,\Theta\bigr) :: \rho$, halts with result $\mathtt{clockRun}(c_0, k, \Theta, b, n)$ at cost $t$. Here
--   $$ \mathtt{clockBodyBound}(\Theta, k) = \mathtt{stepCostBound}(\Theta) + \mathtt{subBound}(\Theta, k) + \mathtt{stepBound}(\Theta) + \mathtt{sizeBound}(\mathtt{stepBound}\,\Theta) + \mathtt{subBound}(\mathtt{stepBound}\,\Theta, \Theta) + 6\,\mathtt{stepBound}(\Theta) + 12\Theta + 30k + 200 , $$
--   a polynomial in $\Theta$ and $k$ (with $\mathtt{stepBound}(S) = (S+1)(S+40)+200$, $\mathtt{stepCostBound}(S) = (S+1)(7S+32)+13S+50$, $\mathtt{subBound}(a,b) = (a+1)(2a+2b+14)$ and $\mathtt{sizeBound}(s) = (s+1)(5s+20)+s+6$).
--
--   This is the core of the clocked universal machine of blueprint `lem:universal-tm`: `univTProg_runs` applies it from the initial configuration with $n = 0$ and $b = 3k+1$, and identifies $\mathtt{clockRun}$ with the budgeted result `clockedResult` (`clockRun_eq`, from `clockRun_of_final` and `clockRun_of_not`). The bound shows that the loop costs at most polynomially in $k$ and $\Theta$ whether or not the simulated run halts.
--
--   **Formalization Note**: The remaining cost budget in the state is the truncated difference $k - \mathsf{costSum}(c_0, n)$, which hypothesis 2 makes an honest difference; the condition $b \le 3k+1$ is only used to bound the cost of reading the step budget. `clockRun` is a noncomputable definition (it decides finality classically) used purely as a specification. All numerals in the state are unary.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Universal.lean#L1031-L1105; internal lemma of the formalization of blueprint lem:universal-tm, https://vidick.github.io/MIPRE-formalization/blueprint/

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

theorem MIPRE.Cost.Machine.clockLoop_runs (c₀ : Cfg) (k Θ : ℕ) (env : Env) : ∀ (b n : ℕ), b ≤ 3 * k + 1 →
    costSum c₀ n ≤ k → (step^[n] c₀).toData.size ≤ Θ →
    ∃ t ≤ (b + 1) * (clockBodyBound Θ k + 1),
      Eval (clockState (step^[n] c₀).toData (.ofNat (k - costSum c₀ n)) (.ofNat b) (.ofNat Θ)
          :: env) (.loop clockBody) (clockRun c₀ k Θ b n) t := by sorry
