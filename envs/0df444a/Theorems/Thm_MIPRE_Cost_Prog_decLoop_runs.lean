-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_decLoop_runs
-- name    : MIPRE.Cost.Prog.decLoop_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:29:08.3818+00:00
-- url     : https://prove2.me/theorems/bfb6b598-2612-49e1-95de-b27f0ac2536b
-- title:
--   First phase of binary decrement: flipping the trailing zeros onto an accumulator, within cost $(j+1)(S+15)$
-- statement:
--   In the ambient cost model (binary-tree data, $\mathrm{size}$ = number of nodes, bit strings encoded as `cons`-chains of bits, numerals written least significant bit first, timed semantics $\mathrm{Eval}(\mathrm{env}, p, r, t)$ charging one unit per rule plus the size of every value read), the decrement program `decProg` works in two phases. This lemma analyzes the first phase, the loop `loop decBody`, whose state is a pair $(\mathrm{bits}, \mathrm{acc})$: as long as the leading bit of $\mathrm{bits}$ is $0$ it is removed and a $1$ is pushed onto the accumulator; at the first $1$ bit the loop stops with the pair $(0 \cdot \mathrm{acc}, \mathrm{rest})$, where $\mathrm{rest}$ is what follows that bit.
--
--   Let $j, i \in \mathbb{N}$, let $r \in \{0,1\}^*$, let $\mathrm{env}$ be any environment and let $S \in \mathbb{N}$ satisfy
--
--   $$ 2j + \mathrm{size}(\mathrm{encode}(r)) + 4 \;+\; (4i + 1) \;+\; 2j \;\le\; S. $$
--
--   Here $2j + \mathrm{size}(\mathrm{encode}(r)) + 4$ is exactly the size of the encoded input string $0^j 1 r$, $4i+1$ is exactly the size of the encoded accumulator $1^i$, and the additional $2j$ covers the growth of the state during the loop (each converted bit removes two nodes from the string and adds four to the accumulator). Then there is a cost $t$ with
--
--   $$ t \le (j+1)(S+15) \quad\text{and}\quad \mathrm{Eval}\bigl(\texttt{cons}(\mathrm{encode}(0^j 1 r), \mathrm{encode}(1^i)) :: \mathrm{env},\ \texttt{loop decBody},\ \texttt{cons}(\mathrm{encode}(0\,1^{i+j}), \mathrm{encode}(r)),\ t\bigr): $$
--
--   started on the state $(0^j 1 r, 1^i)$, the loop halts with the pair $(0\,1^{i+j}, r)$.
--
--   The lemma is the inductive core of `decProg_runs`, the cost analysis of binary decrement (the second phase reverses $0\,1^{j}$ onto $r$ to obtain $1^j 0 r$); decrement, in turn, is one of the two arithmetic primitives of the bit-query program behind succinct descriptions.
--
--   **Formalization Note**. The statement is about the loop `Prog.loop decBody` of `MIPRE.Cost.Prog.decProg`, with the generalized accumulator $1^i$ needed for the induction. The slack hypothesis on $S$ is stated with the explicit sizes $2j + \mathrm{size}(\mathrm{encode}\,r) + 4$ and $4i+1$ so that the bound $(j+1)(S+15)$ is a single product; each iteration costs at most $S + 15$ because the loop state is copied by `var` reads whose cost is its size. The strings are lists of Booleans (`List Bool`) with the least significant bit first, and $0^j 1 r$ is `List.replicate j false ++ true :: rest`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Numeric.lean#L237-L272; internal lemma of the formalization of blueprint def:succinct (first phase of the binary decrement used by the bit-indexing program `bitAtProg`)

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog

theorem MIPRE.Cost.Prog.decLoop_runs (j : ℕ) (rest : BitStr) (i : ℕ) (env : Env) (S : ℕ)
    (hS : 2 * j + (encode rest).size + 4 + (4 * i + 1) + 2 * j ≤ S) :
    ∃ t ≤ (j + 1) * (S + 15),
      Eval (.cons (encode (List.replicate j false ++ true :: rest))
          (encode (List.replicate i true)) :: env) (.loop decBody)
        (.cons (encode (false :: List.replicate (i + j) true)) (encode rest)) t := by sorry
