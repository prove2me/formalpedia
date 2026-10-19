-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_coordLoop_inv
-- name    : MIPRE.Cost.Prog.coordLoop_inv
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:24:49.3565+00:00
-- url     : https://prove2.me/theorems/c2b9b7c2-e8c1-43b6-8571-70871c9f3e03
-- title:
--   The loop accepts only on DecAcc
-- statement:
--   A statement of the module `MIPRE.Foundations.Repeat.DecLoop` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The coordinate loop of the repeated decider. The repeated decider of `thm:parallel-repetition` runs the input decider `D̄` on each of the `k` coordinates of its input (`planning/repetition-verifier.md`, R3(c)). This module is that loop, on the state `(k, remX, remY, remA, remB, ctx)` — `k` a unary counter, `remX, remY` the questions still to be cut into blocks of `s`, `remA, remB` the answers still to be checked, `ctx = (D̄, n, s, B)`: * `preProg` cuts a block off `remX` and `remY`, checks that the current answers are bit strings of length at most `B` (`okBits`), and returns the query `(D̄,…
--
--   **The loop accepts only on `DecAcc`.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Cost
--   open MIPRE.Cost.Prog
--   open MIPRE.Cost.Data
--
--   theorem MIPRE.Cost.Prog.coordLoop_inv {univ : Prog} (hU : univ.WellScoped 1) (dD nD : Data) (s B : ℕ) :
--       ∀ (k : ℕ) (remX remY remA remB : List Data) (env : Env) {t : ℕ},
--         Eval (decState (ofNat k) remX remY remA remB (decCtx dD nD s B) :: env)
--           (.loop (coordBody univ)) (.cons .nil .nil) t →
--         DecAcc univ dD nD s B k remX remY remA remB
--   ```
--
--   **Formalization Note** `MIPRE.Cost.Prog.coordLoop_inv` is declared in `MIPRE/Foundations/Repeat/DecLoop.lean`, lines 691–759. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Repeat/DecLoop.lean#L691-L759

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
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
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Repeat_DecLoop

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open MIPRE.Cost.Data

theorem MIPRE.Cost.Prog.coordLoop_inv {univ : Prog} (hU : univ.WellScoped 1) (dD nD : Data) (s B : ℕ) :
    ∀ (k : ℕ) (remX remY remA remB : List Data) (env : Env) {t : ℕ},
      Eval (decState (ofNat k) remX remY remA remB (decCtx dD nD s B) :: env)
        (.loop (coordBody univ)) (.cons .nil .nil) t →
      DecAcc univ dD nD s B k remX remY remA remB := by sorry
