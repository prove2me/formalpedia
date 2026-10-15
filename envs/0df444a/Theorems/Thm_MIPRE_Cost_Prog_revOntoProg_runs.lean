-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_revOntoProg_runs
-- name    : MIPRE.Cost.Prog.revOntoProg_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:28:27.184993+00:00
-- url     : https://prove2.me/theorems/26daaaed-c79d-4df0-8a5d-b80b66b5b14a
-- title:
--   List reversal onto an accumulator runs in time $(|l|+1)(S+12)$ in the ambient cost model
-- statement:
--   In the ambient cost model of the formalization, data are binary trees built from $\mathtt{nil}$ and $\mathtt{cons}$, and $\mathrm{size}(d)$ is the number of nodes of a tree $d$ ($\mathtt{nil}$ counting one). A finite list $l = [a_1, \dots, a_n]$ of data is represented as the $\mathtt{cons}$-chain $\mathrm{list}(l) = \mathtt{cons}(a_1, \mathtt{cons}(a_2, \dots, \mathtt{nil}))$ (`Data.list`), so that $\mathrm{size}(\mathrm{list}(l)) = 1 + \sum_{i}(\mathrm{size}(a_i) + 1)$. Programs are terms of a small first-order language with de Bruijn variables, and the timed big-step semantics $\rho \vdash p \Downarrow_t r$ (`Eval`) states that the program $p$, run in the environment $\rho$ (a list of values, variable $0$ first), halts with result $r$ at cost $t$: each rule costs one unit, and reading a variable additionally costs the size of the value read.
--
--   The program `revOntoProg` is a single `loop` whose state, held in variable $0$, is a pair $\mathtt{cons}(xs, acc)$: an iteration on a non-empty $xs = h :: xs'$ continues with the state $\mathtt{cons}(xs', h :: acc)$, and on $xs = \mathtt{nil}$ the loop stops with the result $acc$.
--
--   **Statement.** Let $l$ and $acc$ be lists of data, let $\rho$ be an arbitrary environment, and let $S \in \mathbb{N}$ satisfy $\mathrm{size}(\mathrm{list}(l)) + \mathrm{size}(\mathrm{list}(acc)) \le S$. Then there is a cost $t$ such that
--
--   $$ t \le (|l| + 1)\,(S + 12) \qquad\text{and}\qquad \mathtt{cons}(\mathrm{list}(l), \mathrm{list}(acc)) :: \rho \;\vdash\; \mathtt{revOntoProg} \;\Downarrow_t\; \mathrm{list}\bigl(\mathrm{reverse}(l) \mathbin{+\!\!+} acc\bigr), $$
--
--   where $|l|$ is the length of $l$ and $\mathbin{+\!\!+}$ is list concatenation.
--
--   This is a primitive of the closure library of the cost model (its second part, on loops). Plain reversal `revProg` is this program started with an empty accumulator, and the binary decrement `decProg` of the numeric library uses `revOntoProg` as its second phase, to put the flipped low-order bits back in front of the untouched high-order bits. The decrement is in turn the index-walking step of the bit-query program `bitAtProg`, whose cost fixes the time budget $(n+1)(|m|+1)^2$ in the definition of a succinct description (`IsSuccinctDesc`, blueprint `def:succinct`).
--
--   **Formalization Note**: The bound is stated with a free parameter $S$ dominating the sizes involved, in the form $(\text{iterations}+1)(S + c)$ common to the loop library, so that it is a single atom for linear arithmetic during the induction; the environment $\rho$ below the loop state is arbitrary, as needed when the loop sits under `let_` binders. The constants are those of the model: an iteration on $h :: xs'$ with accumulator $acc$ costs exactly $\mathrm{size}(\mathrm{list}(xs')) + \mathrm{size}(h) + \mathrm{size}(\mathrm{list}(acc)) + 12$ (including the unit of the loop rule), and the final test costs $\mathrm{size}(\mathrm{list}(acc)) + 6$.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Loops.lean#L133-L158; internal lemma of the formalization of blueprint def:succinct (closure library, part II: loops; consumed by the binary decrement of the bit-query program)

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog

theorem MIPRE.Cost.Prog.revOntoProg_runs (l acc : List Data) (env : Env) (S : ℕ)
    (hS : (Data.list l).size + (Data.list acc).size ≤ S) :
    ∃ t ≤ (l.length + 1) * (S + 12),
      Eval (.cons (.list l) (.list acc) :: env) revOntoProg (.list (l.reverse ++ acc)) t := by sorry
