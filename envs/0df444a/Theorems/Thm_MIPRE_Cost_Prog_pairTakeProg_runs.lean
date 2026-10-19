-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_pairTakeProg_runs
-- name    : MIPRE.Cost.Prog.pairTakeProg_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:25:21.739023+00:00
-- url     : https://prove2.me/theorems/de076c2c-c654-486e-ab06-e712858fbd0b
-- title:
--   Lemma pairTakeProg_runs of the MIP* = RE formalization
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
--   theorem MIPRE.Cost.Prog.pairTakeProg_runs (s : ℕ) (remU remY : List Data) :
--       ∃ t ≤ pairTakeCost s (list remU).size (list remY).size,
--         pairTakeProg.Runs (.cons (ofNat s) (.cons (list remU) (list remY)))
--           (.cons (list (remU.drop s)) (.cons (list (remY.drop s))
--             (.cons (list (remU.take s)) (list (remY.take s))))) t
--   ```
--
--   **Formalization Note** `MIPRE.Cost.Prog.pairTakeProg_runs` is declared in `MIPRE/Foundations/Repeat/MapLoop.lean`, lines 65–132. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Repeat/MapLoop.lean#L65-L132

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

theorem MIPRE.Cost.Prog.pairTakeProg_runs (s : ℕ) (remU remY : List Data) :
    ∃ t ≤ pairTakeCost s (list remU).size (list remY).size,
      pairTakeProg.Runs (.cons (ofNat s) (.cons (list remU) (list remY)))
        (.cons (list (remU.drop s)) (.cons (list (remY.drop s))
          (.cons (list (remU.take s)) (list (remY.take s))))) t := by sorry
