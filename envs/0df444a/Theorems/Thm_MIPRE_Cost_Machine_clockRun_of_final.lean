-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_clockRun_of_final
-- name    : MIPRE.Cost.Machine.clockRun_of_final
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:29:49.488393+00:00
-- url     : https://prove2.me/theorems/27858064-d83e-42e3-967c-501ea03f25db
-- title:
--   `clockRun` returns the flagged value on a run that halts within the cost budget and the size guard
-- statement:
--   Let $\mathtt{clockRun}(c_0, k, \Theta, b, n)$ be the specification of the clocked interpreter loop: starting from the $n$-th configuration $\mathsf{step}^{n}(c_0)$ of the machine run of $c_0$, with $b$ further iterations allowed, it is the flagged value $\mathsf{cons}\,(\mathsf{cons}\,\mathsf{nil}\,\mathsf{nil})\,r$ if the current configuration is final with value $r$; otherwise it is $\mathsf{nil}$ if $b = 0$, and for $b = b'+1$ it is $\mathtt{clockRun}(c_0, k, \Theta, b', n+1)$ when the cumulative cost $\mathsf{costSum}(c_0, n+1)$ of the first $n+1$ steps is at most $k$ and the encoded size of the $(n+1)$-st configuration is at most $\Theta$, and $\mathsf{nil}$ otherwise.
--
--   Let $c_0$ be a configuration, $k, \Theta, N \in \mathbb{N}$, $r$ a value and $e$ an environment. Suppose that
--   1. $\mathsf{step}^{N}(c_0) = \langle\mathsf{ret}\,r, e, [\,]\rangle$ (the run reaches a final configuration with value $r$ at step $N$),
--   2. $\mathsf{costSum}(c_0, N) \le k$ (it does so within the cost budget), and
--   3. $\mathrm{size}\lceil\mathsf{step}^{n}(c_0)\rceil \le \Theta$ for all $n$ (every configuration of the run is within the guard).
--
--   Then for all $b, n$ with $n \le N \le n + b$,
--   $$ \mathtt{clockRun}(c_0, k, \Theta, b, n) = \mathsf{cons}\,(\mathsf{cons}\,\mathsf{nil}\,\mathsf{nil})\,r . $$
--
--   Together with `clockRun_of_not` (the timeout case) this identifies the value of the clocked loop with the budgeted result `clockedResult` (`clockRun_eq`): a run of cost $t \le k$ takes at most $3t \le 3k$ machine steps (`eval_steps_count`), so the step budget $3k+1$ suffices. It serves the clocked universal machine of blueprint `lem:universal-tm`.
--
--   **Formalization Note**: `clockRun` is the noncomputable specification function of `Cost/Universal.lean` (finality is decided classically); the statement is purely about it and the machine, not about any program. Hypothesis 3 is demanded for all $n$, which is harmless since final configurations are fixed. The conclusion holds for every $n \le N$, not only $n = 0$, as required by the induction.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Universal.lean#L1107-L1136; internal lemma of the formalization of blueprint lem:universal-tm, https://vidick.github.io/MIPRE-formalization/blueprint/

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

theorem MIPRE.Cost.Machine.clockRun_of_final (c₀ : Cfg) (k Θ : ℕ) (N : ℕ) (r : Data) (e : Env)
    (hN : step^[N] c₀ = ⟨.ret r, e, []⟩) (hcost : costSum c₀ N ≤ k)
    (hΘ : ∀ n, (step^[n] c₀).toData.size ≤ Θ) :
    ∀ b n, n ≤ N → N ≤ n + b → clockRun c₀ k Θ b n = .cons (.cons .nil .nil) r := by sorry
