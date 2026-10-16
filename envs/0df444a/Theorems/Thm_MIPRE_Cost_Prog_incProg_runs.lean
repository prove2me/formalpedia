-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_incProg_runs
-- name    : MIPRE.Cost.Prog.incProg_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:26:00.311565+00:00
-- url     : https://prove2.me/theorems/d1ee96c1-7358-4c26-ad0f-cd879026254b
-- title:
--   The increment program computes the successor of a binary numeral within an explicit cost bound
-- statement:
--   Let $l$ be a bit string, read as a binary numeral least significant bit first, and let `inc l` be its successor ($[] \mapsto [\mathrm{true}]$, $\mathrm{false} :: l \mapsto \mathrm{true} :: l$, $\mathrm{true} :: l \mapsto \mathrm{false} :: \mathrm{inc}\ l$). The increment program is `incProg = let_ (cons (var 0) nil) (let_ (loop incBody) revOntoProg)`: it pairs the input with an empty accumulator, runs the carry loop `incBody` (which moves the carried bits onto the accumulator and stops at the first `false` bit or at the end), and reverses the accumulator back onto the rest with `revOntoProg`. `p.Runs x r t` means `Eval [x] p r t`: the program $p$ on the input $x$ halts with result $r$ at cost $t$, in the timed big-step semantics of the ambient model. Then
--
--   $$\exists\, t \le (|l| + 2)\,\big(8\,|\mathrm{encode}\ l| + 8\,|l| + 60\big),\qquad \mathrm{incProg}.\mathrm{Runs}\ (\mathrm{encode}\ l)\ (\mathrm{encode}\ (\mathrm{inc}\ l))\ t ,$$
--
--   where $|\mathrm{encode}\ l|$ is the size (node count) of the encoded string.
--
--   `incProg_runs_nat` specializes this to canonical numerals `n.bits`, where `inc n.bits = (n + 1).bits`; that is the form in which the compressor's reading loop steps from the bit query $i$ to $i + 1$.
--
--   **Formalization Note** `encode l` is the list encoding `Data.ofList Data.ofBool l`, of size at most $4|l| + 1$ (`esize_bitStr_le`), so the bound is quadratic in $|l|$. `inc` is defined on all bit strings and the statement assumes no canonicity (no condition on the last bit). `incProg` is closed (`incProg_wellScoped`). The argument `l` is explicit and the proposition is `MIPRE.Cost.Prog.incProg_runs`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Arith.lean#L298-L346

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
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
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open Polynomial
open MIPRE.Cost.Data

theorem MIPRE.Cost.Prog.incProg_runs (l : BitStr) :
    ∃ t ≤ (l.length + 2) * (8 * (encode l : Data).size + 8 * l.length + 60),
      incProg.Runs (encode l) (encode (inc l)) t := by sorry
