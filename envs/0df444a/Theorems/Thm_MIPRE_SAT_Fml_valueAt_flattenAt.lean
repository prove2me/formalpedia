-- Prove2me | Theorems.Thm_MIPRE_SAT_Fml_valueAt_flattenAt
-- name    : MIPRE.SAT.Fml.valueAt_flattenAt
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:26:36.022667+00:00
-- url     : https://prove2.me/theorems/d4385d9a-f8f1-4ddf-bad8-ab9fe2730930
-- title:
--   The output gate of flattenAt placed after pre computes the formula, whatever follows
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.Formula` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Boolean formulas and their circuits. A formula (`Fml`) is a tree of `and`, `or`, `not` over input bits and constants. Its post-order flattening (`Fml.flattenAt`) is a circuit in which every gate is read at most once (input bits are read through fresh `input` gates, which `Circuit.WellFormed` does not count), so a formula's circuit is well-formed whatever the formula (`Fml.toCircuit_wellFormed`), and computes the formula (`Fml.eval_toCircuit`). The describer of the succinct Cook–Levin theorem is built as a formula, which confines the circuit bookkeeping to this file…
--
--   The output gate of `flattenAt` placed after `pre` computes the formula, whatever follows.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.SAT.Fml
--   open MIPRE.Cost
--
--   theorem MIPRE.SAT.Fml.valueAt_flattenAt (n : ℕ) (x : ℕ → Bool) :
--       ∀ (f : Fml) (pre post : List Gate),
--         (Circuit.mk n (pre ++ f.flattenAt pre.length ++ post)).valueAt x (pre.length + f.size - 1) =
--           f.eval x
--   ```
--
--   **Formalization Note** `MIPRE.SAT.Fml.valueAt_flattenAt` is declared in `MIPRE/Foundations/SAT/Formula.lean`, lines 490–610. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/Formula.lean#L490-L610

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.Fml
open MIPRE.Cost

theorem MIPRE.SAT.Fml.valueAt_flattenAt (n : ℕ) (x : ℕ → Bool) :
    ∀ (f : Fml) (pre post : List Gate),
      (Circuit.mk n (pre ++ f.flattenAt pre.length ++ post)).valueAt x (pre.length + f.size - 1) =
        f.eval x := by sorry
