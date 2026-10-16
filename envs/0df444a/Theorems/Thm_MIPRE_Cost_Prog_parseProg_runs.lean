-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_parseProg_runs
-- name    : MIPRE.Cost.Prog.parseProg_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:38:25.726975+00:00
-- url     : https://prove2.me/theorems/7e9ab2f7-60ca-4678-bec3-12a4c9030984
-- title:
--   `parseProg` reads a serialization back: on the encoded bit string $x$ it computes `parse x` in quadratic time
-- statement:
--   Ambient cost model: data are binary trees (`Data`, with $\mathrm{size}$ the number of nodes), $\mathrm{encode}$ is the size-faithful encoding (a bit string of length $n$ encodes as a $\mathtt{cons}$-chain of bits, of size between $2n + 1$ and $4n + 1$), and $p(v) \Downarrow_t r$ (`p.Runs v r t`) means that the program $p$ on the single input $v$ halts with result $r$ at cost $t$. Description strings are postorder serializations of data (`Data.toBitsPost`), read back by the stack machine of `Data.stackRun`: a $0$ pushes $\mathtt{nil}$, a $1$ pops two entries and pushes their pair; the total reader $\mathrm{parse}(x)$ = `Data.parse x` is the top of the stack after running the machine over $x$ from the empty stack, $\mathtt{nil}$ if that stack is empty. `parseProg` is the program of the ambient model that pairs its input with the empty stack and runs the loop `parseBody` (`parseLoop_runs`).
--
--   For every bit string $x$:
--
--   $$ \exists\, t \le (|x| + 2)\bigl(\mathrm{size}(\mathrm{encode}\ x) + 2|x| + 25\bigr):\qquad \mathrm{parseProg}(\mathrm{encode}\ x) \Downarrow_t \mathrm{parse}(x). $$
--
--   Since $\mathrm{size}(\mathrm{encode}\ x) \le 4|x| + 1$, the cost is quadratic in $|x|$. `parseProg` is the program with which the compressor's decider reads the description it is handed (`Halting/Compressor.lean`); together with `serProg`, which writes a serialization, it moves between a datum and its description string inside the model.
--
--   **Formalization Note**. The theorem is `MIPRE.Cost.Prog.parseProg_runs (x : BitStr)`, with conclusion `∃ t ≤ (x.length + 2) * ((encode x : Data).size + 2 * x.length + 25), parseProg.Runs (encode x) (parse x) t`. `parseProg` is `.let_ (.cons (.var 0) .nil) (.loop parseBody)` and `parse x = (stackRun x []).headD nil`; `Prog.Runs p v r t` is `Eval [v] p r t`. The bound is an explicit polynomial in $|x|$ and $\mathrm{size}(\mathrm{encode}\ x)$, not an asymptotic statement, and no hypothesis on $x$ is needed: the reader is total, since the stack machine ignores a `1` on a stack with fewer than two entries.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Serial.lean#L200-L215; internal lemma of the formalization of the halting reduction (the reader of description strings, in the ambient model)

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Serial

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open MIPRE.Cost.Data

theorem MIPRE.Cost.Prog.parseProg_runs (x : BitStr) :
    ∃ t ≤ (x.length + 2) * ((encode x : Data).size + 2 * x.length + 25),
      parseProg.Runs (encode x) (parse x) t := by sorry
