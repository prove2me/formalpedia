-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_decProg_runs
-- name    : MIPRE.Cost.Prog.decProg_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:29:22.061369+00:00
-- url     : https://prove2.me/theorems/19ed6a5b-e8a4-4adc-9720-53fffd9a2898
-- title:
--   Binary decrement $0^j 1 r \mapsto 1^j 0 r$ runs within cost $(j+2)\bigl(10\,\mathrm{size}(\mathrm{input}) + 60\bigr)$
-- statement:
--   In the ambient cost model (binary-tree data with $\mathrm{size}$ the number of nodes, bit strings encoded as `cons`-chains of bits, numerals written least significant bit first), let `decProg` be the fixed decrement program. A nonzero binary numeral has the form $0^j 1 r$ (its $j$ least significant bits are $0$, followed by a $1$ and a remainder $r \in \{0,1\}^*$), and its predecessor is $1^j 0 r$: the trailing zeros become ones and the first one becomes a zero.
--
--   Let $j \in \mathbb{N}$ and $r \in \{0,1\}^*$. Then there is a cost $t$ with
--
--   $$ t \le (j+2)\,\bigl(10\,(2j + \mathrm{size}(\mathrm{encode}(r)) + 4) + 60\bigr) $$
--
--   such that `decProg`, run on the input $\mathrm{encode}(0^j 1 r)$, halts with result $\mathrm{encode}(1^j 0 r)$ at cost $t$ (`Prog.Runs`: the run in the one-entry environment holding the input). Here $2j + \mathrm{size}(\mathrm{encode}(r)) + 4$ is exactly the size of the encoded input, so the bound is quadratic in the size of the input.
--
--   Decrement is one of the two arithmetic primitives of the bit-query program `bitAtProg`: to answer a query for the $m$-th bit of a string, that program walks the string while decrementing the binary index $m$, testing it for zero at each step. Since every string with a $1$ bit splits as $0^j 1 r$, this lemma yields (as `decProg_runs'`) a decrement of every nonzero index within the bound `decBound` of the bit-query analysis, which is where the factor $(|m|+1)^2$ of the time budget in the definition of a succinct description comes from.
--
--   **Formalization Note**. `MIPRE.Cost.Prog.decProg` is `let_ (cons (var 0) nil) (let_ (loop decBody) revOntoProg)`: pair the input with an empty accumulator, run the first phase (`decLoop_runs`), then reverse the accumulated prefix onto the remainder (`revOntoProg_runs`). The output may be a non-canonical numeral (it can end in $0$ bits when $r$ does), which is why the specification is by the shape $1^j 0 r$, and the bit-query analysis then speaks of the value `bitsVal` of a bit string rather than of `Nat.bits`. The constant $60$ and the factor $10$ absorb the two phases' bounds $(j+1)(S_1+15)$ and $(j+2)(S_2+12)$ and the pairing prefix.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Numeric.lean#L274-L324; internal lemma of the formalization of blueprint def:succinct (the binary decrement used by the bit-indexing program `bitAtProg`)

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

theorem MIPRE.Cost.Prog.decProg_runs (j : ℕ) (rest : BitStr) :
    ∃ t ≤ (j + 2) * (10 * (2 * j + (encode rest).size + 4) + 60),
      decProg.Runs (encode (List.replicate j false ++ true :: rest))
        (encode (List.replicate j true ++ false :: rest)) t := by sorry
