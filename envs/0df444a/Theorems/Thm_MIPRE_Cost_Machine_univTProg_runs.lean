-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_univTProg_runs
-- name    : MIPRE.Cost.Machine.univTProg_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:29:50.072327+00:00
-- url     : https://prove2.me/theorems/15074767-b8f2-4895-8fc9-3e26a95e8d4e
-- title:
--   The clocked universal program returns the budgeted result `clockedResult c v k` in time polynomial in $k + |c| + |v|$
-- statement:
--   Fix the ambient cost model: programs $c \in \mathsf{Prog}$ act on values $v \in \mathsf{Data}$ (binary trees), $\mathsf{Eval}\;[v]\;c\;r\;t$ (in Lean `c.Runs v r t`) says that $c$ on input $v$ halts with result $r$ at cost $t$, every program is encoded as a value $\lceil c\rceil$ (`encode c`, the tree encoding `Prog.toData`) of size $|c| = \mathrm{esize}(c)$, and natural numbers used as budgets are passed in unary, $\mathsf{ofNat}(k)$ being the list of $k$ copies of $\mathsf{nil}$. The *budgeted result* of $c$ on $v$ under the cost budget $k$ is
--   $$ \mathtt{clockedResult}(c, v, k) = \begin{cases} \mathsf{cons}\,(\mathsf{cons}\,\mathsf{nil}\,\mathsf{nil})\,r & \text{if } c \text{ halts on } v \text{ with result } r \text{ at some cost } t \le k, \\ \mathsf{nil} & \text{otherwise (timeout)}, \end{cases} $$
--   which is well defined because the semantics is deterministic.
--
--   `univTProg` is a fixed closed program, the clocked self-interpreter: on the input $(\mathsf{ofNat}\,k, (\lceil c\rceil, v))$ it computes $X = k + |c| + |v|$ and a size guard $\Theta(X)$ in unary, builds the initial configuration of the evaluation machine for $c$ on $v$, and runs the clocked interpreter loop with cost budget $k$, step budget $3k+1$ and guard $\Theta(X)$. The theorem states its correctness and its time bound.
--
--   For every program $c$, every value $v$ and every $k \in \mathbb{N}$ there is a cost
--   $$ t \le \mathtt{univTBoundFun}(k + |c| + |v|) $$
--   such that `univTProg`, run on the single input $\mathsf{cons}\,(\mathsf{ofNat}\,k)\,(\mathsf{cons}\,\lceil c\rceil\,v)$, halts with result $\mathtt{clockedResult}(c, v, k)$ at cost $t$. The function $\mathtt{univTBoundFun}$ is an explicit polynomial (`univTPoly`): with $Y(X) = 9X + 4$, $T_1(X) = Y(2Y+2) + 1$ and $\Theta(X) = Y(T_1 + 1) + 1$,
--   $$ \mathtt{univTBoundFun}(X) = 2\,\mathtt{sizeBound}(X) + 2\,\mathtt{addBound}(X,X) + 2\,\mathtt{tripleBound}(X,1) + \mathtt{tripleBound}(3X+1,1) + \mathtt{repBound}(Y, 2Y+1, 1) + \mathtt{repBound}(Y, T_1, 1) + \mathtt{sizeBound}(\Theta) + (3X+2)\bigl(\mathtt{clockBodyBound}(\Theta, X) + 1\bigr) + 20\Theta + 20T_1 + 60Y + 100X + 500 , $$
--   where $\mathtt{sizeBound}$, $\mathtt{addBound}$, $\mathtt{tripleBound}$, $\mathtt{repBound}$ are the (quadratic) cost bounds of the unary size, addition, tripling and replication programs and $\mathtt{clockBodyBound}(\Theta, k)$ is the polynomial cost bound of one iteration of the clocked loop.
--
--   This theorem is the `run` field of the clocked universal machine `selfClockedUniversal`, and so proves `exists_clocked_universal`, half of blueprint `lem:universal-tm` ([MNY, Lemma 2.1]). The clocked machine is the primitive with which the deciders of the compression pipeline simulate other deciders under a budget, and with which the recursive compression argument runs a description "for $\log n$ steps".
--
--   **Formalization Note**: The budget $k$ counts cost units of the big-step semantics (not machine steps), is supplied in unary (so the input has size $2k + 1 + |c| + |v| + 2$), and the bound is polynomial in $k$ itself. The result is total: the program halts on every input, also when the simulated run does not halt, which is what the step budget $3k+1$ and the size guard $\Theta$ are for; the guard never fires on a run that halts within the budget, whose configurations have size at most $\mathtt{sigmaFun}(X) \le \Theta(X)$. The constants in the bound are those produced by the proof.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Universal.lean#L1251-L1407; internal lemma of the formalization of blueprint lem:universal-tm, https://vidick.github.io/MIPRE-formalization/blueprint/

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

theorem MIPRE.Cost.Machine.univTProg_runs (c : Prog) (v : Data) (k : ℕ) :
    ∃ t ≤ univTBoundFun (k + esize c + v.size),
      univTProg.Runs (.cons (.ofNat k) (.cons (encode c) v)) (clockedResult c v k) t := by sorry
