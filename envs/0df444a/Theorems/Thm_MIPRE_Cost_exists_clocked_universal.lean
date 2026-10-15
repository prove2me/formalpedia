-- Prove2me | Theorems.Thm_MIPRE_Cost_exists_clocked_universal
-- name    : MIPRE.Cost.exists_clocked_universal
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:29:58.564285+00:00
-- url     : https://prove2.me/theorems/1b53b891-32ae-4d62-a195-004aba1772fb
-- title:
--   Existence of a clocked universal machine: total, budgeted simulation in polynomial time
-- statement:
--   Fix the ambient cost model: programs $c$ run on values $v$ (binary trees), $\mathsf{Eval}\;[v]\;c\;r\;t$ (`c.Runs v r t`) says that $c$ halts on $v$ with result $r$ at cost $t$, programs are encoded as values $\lceil c\rceil$ of size $|c|$, and budgets are passed in unary, $\mathsf{ofNat}(k)$ being the list of $k$ copies of $\mathsf{nil}$. The *budgeted result* of $c$ on $v$ under the cost budget $k$ is
--   $$ \mathtt{clockedResult}(c, v, k) = \begin{cases} \mathsf{cons}\,(\mathsf{cons}\,\mathsf{nil}\,\mathsf{nil})\,r & \text{if } c \text{ halts on } v \text{ with result } r \text{ at some cost } t \le k, \\ \mathsf{nil} & \text{otherwise (timeout)}. \end{cases} $$
--
--   A *clocked universal machine* (`ClockedUniversalMachine`) is a structure consisting of a closed program $u_T$ (reading only its input) and a polynomial $p \in \mathbb{N}[X]$ such that for every program $c$, every input $v$ and every budget $k \in \mathbb{N}$ there is a cost
--   $$ t \le p\bigl(k + |c| + |v|\bigr) \quad\text{with}\quad \mathsf{Eval}\;\bigl[\mathsf{cons}\,(\mathsf{ofNat}\,k)\,(\mathsf{cons}\,\lceil c\rceil\,v)\bigr]\;u_T\;\mathtt{clockedResult}(c, v, k)\;t . $$
--   The theorem states that such a machine exists:
--   $$ \mathsf{Nonempty}\;\mathtt{ClockedUniversalMachine} . $$
--
--   In words: there is a fixed program that, given $k$, a program $c$ and an input $v$, runs $c$ on $v$ for cost at most $k$ and reports either the result or a timeout, always halting, and does so in time polynomial in $k + |c| + |v|$. This is the time-bounded half of blueprint `lem:universal-tm` (efficient universal Turing machine, [MNY, Lemma 2.1]). It is the primitive with which the deciders of the compression pipeline (introspection, parallel repetition) simulate other deciders under a budget, and with which the recursive compression argument runs a description $e$ "for $\log n$ steps"; because the machine is a structure, downstream definitions can refer to its program and its overhead polynomial as data.
--
--   **Formalization Note**: The budget $k$ counts cost units of the big-step semantics and is given in unary, so a polynomial bound in $k$ is the appropriate notion ("run for $k$ steps" with $k$ written out); the input is the triple encoded as $\mathsf{cons}\,(\mathsf{ofNat}\,k)\,(\mathsf{cons}\,\lceil c\rceil\,v)$. The witness is the clocked self-interpreter `selfClockedUniversal` of `Cost/Universal.lean` (program `univTProg`, polynomial `univTPoly`). The result is total, which the blueprint statement of `lem:universal-tm` does not mention separately: it covers the unclocked machine, and the clocked variant is attached to the same blueprint node.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Universal.lean#L1549-L1550; blueprint lem:universal-tm, https://vidick.github.io/MIPRE-formalization/blueprint/; [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Lemma 2.1

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
open Polynomial

theorem MIPRE.Cost.exists_clocked_universal : Nonempty ClockedUniversalMachine := by sorry
