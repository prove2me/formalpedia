-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_interpLoop_runs
-- name    : MIPRE.Cost.Machine.interpLoop_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:29:24.303009+00:00
-- url     : https://prove2.me/theorems/a9ac2d14-0548-48cc-8d77-71c99014c318
-- title:
--   The interpreter loop follows a halting machine run, at cost $(m+1)(B(S)+1)$ for $m$ remaining steps
-- statement:
--   The self-interpreter of the ambient cost model drives the evaluation machine: a configuration $c$ (control, environment, stack) is encoded as a value $\lceil c\rceil$ (`Cfg.toData`), and the fixed program `interpBody` acts on such a value as follows: it tests whether the configuration is final (`isFinalProg`), and if so stops the loop with the returned value, and otherwise continues the loop with the encoding of the next configuration, computed by the step program `stepProg`. The interpreter loop is $\mathsf{loop}\;\mathtt{interpBody}$; a $\mathsf{loop}$ of the model iterates its body on the state held in variable $0$ until the body signals stop.
--
--   Let $c_0$ be a configuration and let $S \in \mathbb{N}$ bound the encoded size of every configuration along its run: $\mathrm{size}(\lceil \mathsf{step}^{n}(c_0)\rceil) \le S$ for all $n$. Suppose the run reaches, after $N$ steps, the final configuration with value $r$ and some environment $e$: $\mathsf{step}^{N}(c_0) = \langle \mathsf{ret}\,r, e, [\,]\rangle$. Let $\rho$ be an arbitrary environment (the entries below the loop state, which the loop never reads). Then for all $m, n$ with $n + m = N$ there is a cost
--   $$ t \le (m+1)\bigl(B(S) + 1\bigr), \qquad B(S) = \mathtt{interpBodyBound}(S) = \mathtt{stepBound}(S) + 3S + 30, \quad \mathtt{stepBound}(S) = (S+1)(S+40) + 200, $$
--   such that evaluating $\mathsf{loop}\;\mathtt{interpBody}$ in the environment $\lceil \mathsf{step}^{n}(c_0)\rceil :: \rho$ halts with result $r$ at cost $t$.
--
--   That is, started on the $n$-th configuration of a run that halts at step $N$, the loop halts with the machine's value, and each of the $m = N - n$ remaining iterations costs at most one body bound $B(S)$, quadratic in $S$. This is the forward half of the efficient universal machine (blueprint `lem:universal-tm`): together with the polynomial bound $S$ on configuration sizes along a run of cost $t$ (`size_toData_le`, `eval_steps_bound`) and the bound $N \le 3t$ on the number of machine steps (`eval_steps_count`), it gives the polynomial time overhead of `univProg`.
--
--   **Formalization Note**: The statement is phrased for an arbitrary starting index $n$ with $n + m = N$ so that it can be proved by induction on the remaining number $m$ of steps; the universal program uses it with $n = 0$, $m = N$. The hypothesis on $S$ is required for all $n$, not only $n \le N$ (configurations after the final one are fixed, so this is no loss). The bound counts one unit for the loop rule per iteration and the body bound $B(S)$ dominates both the final iteration ($3S + 30$) and a stepping iteration ($\mathtt{stepBound}(S)$ for `stepProg` plus the copies and the finality test).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Universal.lean#L143-L183; internal lemma of the formalization of blueprint lem:universal-tm, https://vidick.github.io/MIPRE-formalization/blueprint/

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

theorem MIPRE.Cost.Machine.interpLoop_runs (c₀ : Cfg) (S : ℕ) (hS : ∀ n, (step^[n] c₀).toData.size ≤ S)
    (r : Data) (e : Env) (N : ℕ) (hN : step^[N] c₀ = ⟨.ret r, e, []⟩) (env : Env) :
    ∀ m n, n + m = N → ∃ t ≤ (m + 1) * (interpBodyBound S + 1),
      Eval ((step^[n] c₀).toData :: env) (.loop interpBody) r t := by sorry
