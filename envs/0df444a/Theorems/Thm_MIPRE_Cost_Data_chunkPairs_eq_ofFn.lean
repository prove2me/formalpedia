-- Prove2me | Theorems.Thm_MIPRE_Cost_Data_chunkPairs_eq_ofFn
-- name    : MIPRE.Cost.Data.chunkPairs_eq_ofFn
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:25:31.225545+00:00
-- url     : https://prove2.me/theorems/a41375c0-79e4-47ae-a7eb-167888bbb02b
-- title:
--   With the first list of length k · s, the pairs are the k pairs of pieces
-- statement:
--   A statement of the module `MIPRE.Foundations.Repeat.Prims` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Primitives of the repeated sampler and decider. Three loops of the ambient model that the programs of `thm:parallel-repetition` share (`planning/repetition-verifier.md`, R3(a)–(b)): * `powBody`: on the state `(e, bl, bn, acc)` — `e` a unary counter, `bl` and `bn` the bit lists of `λ` and `n`, `acc` a list — prepend `|bl| + |bn|` copies of `nil` to `acc`, `e` times (`powLoop_runs`). With `acc = []` the result is the unary numeral `e · (|λ| + |n|)`; with `acc` the numeral `1` it is the binary numeral `2^{e(|λ| + |n|)}`, the repetition count `k(n)` and the parse length `B(n)` of…
--
--   With the first list of length `k · s`, the pairs are the `k` pairs of pieces.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Cost
--   open MIPRE.Cost.Data
--
--   theorem MIPRE.Cost.Data.chunkPairs_eq_ofFn (s : ℕ) (hs : 0 < s) : ∀ (k : ℕ) (l y : List Data),
--       l.length = k * s → chunkPairs s hs l y = List.ofFn fun i : Fin k => (chunk s i l, chunk s i y)
--   ```
--
--   **Formalization Note** `MIPRE.Cost.Data.chunkPairs_eq_ofFn` is declared in `MIPRE/Foundations/Repeat/Prims.lean`, lines 174–193. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Repeat/Prims.lean#L174-L193

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
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Data

theorem MIPRE.Cost.Data.chunkPairs_eq_ofFn (s : ℕ) (hs : 0 < s) : ∀ (k : ℕ) (l y : List Data),
    l.length = k * s → chunkPairs s hs l y = List.ofFn fun i : Fin k => (chunk s i l, chunk s i y) := by sorry
