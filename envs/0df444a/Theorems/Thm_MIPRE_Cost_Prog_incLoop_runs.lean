-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_incLoop_runs
-- name    : MIPRE.Cost.Prog.incLoop_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:25:34.729074+00:00
-- url     : https://prove2.me/theorems/55182ebc-fa7b-4058-9a06-aaffa69ef736
-- title:
--   The carry loop of the binary increment program runs within an explicit cost bound
-- statement:
--   Binary numerals are bit strings written least significant bit first, and `inc` is their successor: $[] \mapsto [\mathrm{true}]$, $\mathrm{false} :: l \mapsto \mathrm{true} :: l$, $\mathrm{true} :: l \mapsto \mathrm{false} :: \mathrm{inc}\ l$. The increment program works in two phases; the first is the loop of the body `incBody` on a state `cons (encode rest) (encode acc)`: at the end of `rest` or at a `false` bit it stops with the pair `(true :: acc, rest')`, and at a `true` bit it moves a `false` onto `acc` and continues. The function this phase computes is `incAcc : BitStr → BitStr → BitStr × BitStr`, with `incAcc [] acc = (true :: acc, [])`, `incAcc (false :: r) acc = (true :: acc, r)` and `incAcc (true :: r) acc = incAcc r (false :: acc)`.
--
--   Let $l$ and $acc$ be bit strings, `env` an environment (a list of data), and $S$ a natural number with $|\mathrm{encode}\ l| + |\mathrm{encode}\ acc| + 3\,|l| \le S$, where $|\cdot|$ on data is `Data.size`, the number of nodes. Then
--
--   $$\exists\, t \le (|l| + 1)(S + 21),\qquad \mathrm{Eval}\ \big(\mathrm{cons}\ (\mathrm{encode}\ l)\ (\mathrm{encode}\ acc) :: env\big)\ (\mathrm{loop}\ \mathrm{incBody})\ \Big(\mathrm{cons}\ \big(\mathrm{encode}\ (\mathrm{incAcc}\ l\ acc)_1\big)\ \big(\mathrm{encode}\ (\mathrm{incAcc}\ l\ acc)_2\big)\Big)\ t .$$
--
--   This is the main lemma behind `incProg_runs`, the cost bound of the increment program; the increment is what enumerates the bit queries $0, 1, 2, \dots$ in the compressor's decider of the halting reduction.
--
--   **Formalization Note** `Eval env p r t` is the timed big-step semantics of the ambient model; `.loop b` iterates `b` on the state held in variable $0$, where `b` returns `cons flag s'` and a `nil` flag stops the loop with result `s'`. The state is the head of the environment and `env` is an arbitrary tail. `encode` on bit strings is the list encoding `Data.ofList Data.ofBool`, so $|\mathrm{encode}\ l| \le 4|l| + 1$. The bound is stated in terms of the parameter $S$, any number above the given combination of sizes, rather than directly in $l$ and $acc$. All of `l`, `acc`, `env`, `S` are explicit; the proposition is `MIPRE.Cost.Prog.incLoop_runs`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Arith.lean#L263-L296

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

theorem MIPRE.Cost.Prog.incLoop_runs (l acc : BitStr) (env : Env) (S : ℕ)
    (hS : (encode l : Data).size + (encode acc : Data).size + 3 * l.length ≤ S) :
    ∃ t ≤ (l.length + 1) * (S + 21),
      Eval (Data.cons (encode l) (encode acc) :: env) (.loop incBody)
        (Data.cons (encode (incAcc l acc).1) (encode (incAcc l acc).2)) t := by sorry
