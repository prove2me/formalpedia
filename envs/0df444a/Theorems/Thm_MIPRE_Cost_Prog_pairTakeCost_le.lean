-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_pairTakeCost_le
-- name    : MIPRE.Cost.Prog.pairTakeCost_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:25:19.381336+00:00
-- url     : https://prove2.me/theorems/6665fa21-395b-4867-b2a4-53575fe5b257
-- title:
--   Lemma pairTakeCost_le of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.Repeat.MapLoop` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The block loop of the repeated sampler. The repeated sampler of `thm:parallel-repetition` answers a marginal, linear or factor query on `𝔽₂^{k s}` by cutting the vectors of the query into `k` blocks of `s` coordinates, asking the input sampler about each block, and concatenating the answers (`planning/repetition-verifier.md`, R3(b)). This module is that loop: * `pairTakeProg` cuts the first `s` elements off two lists at once; * `mapBody` is the body of the loop, on the state `(s, remU, remY, ctx, acc)`: stop with `acc` once `remU` is exhausted, and otherwise cut a block off `remU` and `remY`,…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Cost
--   open MIPRE.Cost.Prog
--   open MIPRE.Cost.Data
--
--   theorem MIPRE.Cost.Prog.pairTakeCost_le {s U Y Z : ℕ} (h : s + U + Y ≤ Z) :
--       pairTakeCost s U Y ≤ 17 * (Z + 30) ^ 2
--   ```
--
--   **Formalization Note** `MIPRE.Cost.Prog.pairTakeCost_le` is declared in `MIPRE/Foundations/Repeat/MapLoop.lean`, lines 324–337. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Repeat/MapLoop.lean#L324-L337

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
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open MIPRE.Cost.Data

theorem MIPRE.Cost.Prog.pairTakeCost_le {s U Y Z : ℕ} (h : s + U + Y ≤ Z) :
    pairTakeCost s U Y ≤ 17 * (Z + 30) ^ 2 := by sorry
