-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_getListProg_runs
-- name    : MIPRE.Cost.Machine.getListProg_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:27:38.507304+00:00
-- url     : https://prove2.me/theorems/7a7d68d3-c1db-44d3-81c5-1afd57b88de7
-- title:
--   Variable lookup along an encoded environment runs within cost $(|i|+1)(|\mathrm{env}|+|i|+12)$ in the sizes
-- statement:
--   We work in the ambient cost model of the formalization: data are binary trees (`Data`, from `nil` and `cons`), $\mathrm{size}(d)$ is the number of nodes of $d$, and $\mathrm{Eval}(\mathrm{env}, p, r, t)$ is the timed semantics (the program $p$ in the environment $\mathrm{env}$ halts with $r$ at cost exactly $t$; one unit per rule, plus the size of every value read by a variable or literal). The self-interpreter implements, as a program, the step function of a small-step evaluation machine whose configurations are encoded as data: an environment is a `cons`-chain of values, a stack a `cons`-chain of encoded frames, and a program $p$ is its tree encoding $\mathrm{toData}(p)$, a unary tag ($0$ to $6$ for `var`, `nil`, `cons`, `elim`, `let_`, `loop`, `const`) paired with the fields.
--
--   Variable lookup is the one non-constant operation of a machine step. For data $d$ and $n \in \mathbb{N}$ let $\mathrm{getList}(d, n) = \mathrm{left}(\mathrm{right}^{n}(d))$ be the $n$-th element of the `cons`-chain $d$ (`nil` beyond its end), and for data $i$ let $\mathrm{unaryToNat}(i)$ be the length of the right spine of $i$, so that a unary numeral $\mathrm{ofNat}(n)$ ($n$ nested `cons nil`) reads back as $n$. The program `getListProg` is a `loop` on a state $\texttt{cons}(\mathrm{env}, i)$: if $i$ is exhausted it stops with the head of $\mathrm{env}$, otherwise it continues with the tail of $\mathrm{env}$ and the predecessor of $i$.
--
--   Let $i$ and $\mathrm{env}$ be any data and $\mathrm{rest}$ any further environment. Then there is a cost $t$ with
--
--   $$ t \le (\mathrm{size}(i) + 1)\,\bigl(\mathrm{size}(\mathrm{env}) + \mathrm{size}(i) + 12\bigr) \quad\text{and}\quad \mathrm{Eval}\bigl(\texttt{cons}(\mathrm{env}, i) :: \mathrm{rest},\ \texttt{getListProg},\ \mathrm{getList}(\mathrm{env}, \mathrm{unaryToNat}(i)),\ t\bigr). $$
--
--   The lemma supplies the `var` and `elim` cases of the evaluate-step program `stepEvProg`, where a de Bruijn index (a unary numeral) is looked up in the encoded environment; it is the only reason the cost of one interpreter step (`stepProg_runs`) is quadratic rather than linear in the size of the configuration, and so it enters the polynomial overhead of the efficient universal machine.
--
--   **Formalization Note**. The statement is for arbitrary data $i$, not only unary numerals: only the length of the right spine of $i$ matters, and $\mathrm{size}(i)$ bounds it. The bound is quadratic because each iteration copies the remaining environment (its tail is read by a `var`, at a cost equal to its size); the constant $12$ accounts for the fixed `elim`s, `cons`es and the two projections of one iteration. `Data.getList` and `Data.unaryToNat` are defined in `Cost/Codable.lean` as first-order operations so that the same step function is also primitive recursive.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Interpreter.lean#L93-L134; internal lemma of the formalization of blueprint lem:universal-tm (the environment walk of the self-interpreter)

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

theorem MIPRE.Cost.Machine.getListProg_runs (idx env : Data) (rest : Env) :
    ∃ t ≤ (idx.size + 1) * (env.size + idx.size + 12),
      Eval (.cons env idx :: rest) getListProg (Data.getList env (Data.unaryToNat idx)) t := by sorry
