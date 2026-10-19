-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_mapBody_step
-- name    : MIPRE.Cost.Prog.mapBody_step
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:25:19.537656+00:00
-- url     : https://prove2.me/theorems/afa43fd6-7e81-482d-a5b0-e217ac6ac6c7
-- title:
--   One iteration: the block is cut, the call made, its answer pushed reversed onto acc
-- statement:
--   A statement of the module `MIPRE.Foundations.Repeat.MapLoop` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The block loop of the repeated sampler. The repeated sampler of `thm:parallel-repetition` answers a marginal, linear or factor query on `𝔽₂^{k s}` by cutting the vectors of the query into `k` blocks of `s` coordinates, asking the input sampler about each block, and concatenating the answers (`planning/repetition-verifier.md`, R3(b)). This module is that loop: * `pairTakeProg` cuts the first `s` elements off two lists at once; * `mapBody` is the body of the loop, on the state `(s, remU, remY, ctx, acc)`: stop with `acc` once `remU` is exhausted, and otherwise cut a block off `remU` and `remY`,…
--
--   One iteration: the block is cut, the call made, its answer pushed reversed onto `acc`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Cost
--   open MIPRE.Cost.Prog
--   open MIPRE.Cost.Data
--
--   theorem MIPRE.Cost.Prog.mapBody_step {univ : Prog} (hU : univ.WellScoped 1) (s : ℕ) (h : Data)
--       (l remY : List Data) (sD nD kD wD jD : Data) (acc : List Data) {r : Data} {tu : ℕ}
--       (hr : Eval [mapQuery sD nD kD wD jD (list ((h :: l).take s)) (list (remY.take s))] univ r tu) :
--       ∃ t ≤ mapStepCost s (list (h :: l)).size (list remY).size (mapCtx sD nD kD wD jD).size
--           (list acc).size tu,
--         Eval [mapState s (h :: l) remY (mapCtx sD nD kD wD jD) acc] (mapBody univ)
--           (.cons (.cons .nil .nil)
--             (mapState s ((h :: l).drop s) (remY.drop s) (mapCtx sD nD kD wD jD)
--               ((toList r).reverse ++ acc))) t
--   ```
--
--   **Formalization Note** `MIPRE.Cost.Prog.mapBody_step` is declared in `MIPRE/Foundations/Repeat/MapLoop.lean`, lines 204–300. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Repeat/MapLoop.lean#L204-L300

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

theorem MIPRE.Cost.Prog.mapBody_step {univ : Prog} (hU : univ.WellScoped 1) (s : ℕ) (h : Data)
    (l remY : List Data) (sD nD kD wD jD : Data) (acc : List Data) {r : Data} {tu : ℕ}
    (hr : Eval [mapQuery sD nD kD wD jD (list ((h :: l).take s)) (list (remY.take s))] univ r tu) :
    ∃ t ≤ mapStepCost s (list (h :: l)).size (list remY).size (mapCtx sD nD kD wD jD).size
        (list acc).size tu,
      Eval [mapState s (h :: l) remY (mapCtx sD nD kD wD jD) acc] (mapBody univ)
        (.cons (.cons .nil .nil)
          (mapState s ((h :: l).drop s) (remY.drop s) (mapCtx sD nD kD wD jD)
            ((toList r).reverse ++ acc))) t := by sorry
