-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_clockRun_of_not
-- name    : MIPRE.Cost.Machine.clockRun_of_not
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:30:14.03576+00:00
-- url     : https://prove2.me/theorems/2b768f1e-f2aa-41c4-bc8a-ef3d8153d877
-- title:
--   `clockRun` returns the timeout value $\mathsf{nil}$ when the program does not halt within the cost budget
-- statement:
--   Let $c$ be a program of the ambient cost model and $v$ an input, and let $c_0 = \langle\mathsf{ev}\,c, [v], [\,]\rangle$ be the initial configuration of the evaluation machine for $c$ on $v$. Let $\mathtt{clockRun}(c_0, k, \Theta, b, n)$ be the specification of the clocked interpreter loop started on the $n$-th configuration of the run with $b$ further iterations, cost budget $k$ and size guard $\Theta$: it is the flagged value of the current configuration if that is final, and otherwise either $\mathsf{nil}$ (when $b = 0$, when the cumulative cost $\mathsf{costSum}(c_0, n+1)$ would exceed $k$, or when the next configuration exceeds the guard) or the value at the next configuration with one fewer iteration.
--
--   Suppose that $c$ does not halt on $v$ within cost $k$: there are no $r$ and $t \le k$ with $\mathsf{Eval}\;[v]\;c\;r\;t$. Then for all $b, n \in \mathbb{N}$ with $\mathsf{costSum}(c_0, n) \le k$,
--   $$ \mathtt{clockRun}(c_0, k, \Theta, b, n) = \mathsf{nil} . $$
--
--   This is the timeout half of the identification of the clocked loop's value with the budgeted result `clockedResult` (`clockRun_eq`; the other half is `clockRun_of_final`), used by the clocked universal machine of blueprint `lem:universal-tm`.
--
--   **Formalization Note**: The hypothesis is stated with `Prog.Runs c v r t`, that is, a derivation in the one-element environment $[v]$, and the cost $k$ is the cost of the big-step semantics, not a number of machine steps. The guard $\Theta$ plays no role in the conclusion. The condition $\mathsf{costSum}(c_0, n) \le k$ is what the recursion of `clockRun` maintains; at $n = 0$ it is trivial.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Universal.lean#L1138-L1157; internal lemma of the formalization of blueprint lem:universal-tm, https://vidick.github.io/MIPRE-formalization/blueprint/

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

theorem MIPRE.Cost.Machine.clockRun_of_not (c : Prog) (v : Data) (k Θ : ℕ)
    (hno : ¬ ∃ r t, t ≤ k ∧ c.Runs v r t) :
    ∀ b n, costSum ⟨.ev c, [v], []⟩ n ≤ k → clockRun ⟨.ev c, [v], []⟩ k Θ b n = .nil := by sorry
