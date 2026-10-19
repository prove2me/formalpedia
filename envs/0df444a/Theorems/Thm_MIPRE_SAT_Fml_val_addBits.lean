-- Prove2me | Theorems.Thm_MIPRE_SAT_Fml_val_addBits
-- name    : MIPRE.SAT.Fml.val_addBits
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:26:25.825348+00:00
-- url     : https://prove2.me/theorems/e07bdb54-68b7-40a3-a87b-da8bc58f7233
-- title:
--   The adder identity: sum + 2^W · carry = fs + c + cin
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.FmlLib` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Formulas on bit vectors. The vocabulary in which the describer of the succinct Cook–Levin theorem is written (`planning/succinct-cook-levin.md`, S3): a *field* is a list of formulas read as a binary number, least significant bit first (`Fml.val`); the fields of an index are slices of the input bits (`Fml.field`); and the tests on fields are conjunctions and disjunctions (`andList`, `orList`), equality with a constant or another field (`eqConst`, `eqFields`), comparison (`ltConst`, `ltFields`), addition of a constant with its carry (`addBits`, `addConstRel`), subtraction of a constant by the…
--
--   **The adder identity**: `sum + 2^W · carry = fs + c + cin`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.SAT.Fml
--   open MIPRE.Cost
--
--   theorem MIPRE.SAT.Fml.val_addBits : ∀ (fs : List Fml) (c : BitStr), fs.length = c.length → ∀ (cin : Fml) (x : ℕ → Bool),
--       val (addBits fs c cin).1 x + 2 ^ fs.length * ((addBits fs c cin).2.eval x).toNat =
--         val fs x + bitsVal c + (cin.eval x).toNat
--   ```
--
--   **Formalization Note** `MIPRE.SAT.Fml.val_addBits` is declared in `MIPRE/Foundations/SAT/FmlLib.lean`, lines 368–387. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/FmlLib.lean#L368-L387

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
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
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.Fml
open MIPRE.Cost

theorem MIPRE.SAT.Fml.val_addBits : ∀ (fs : List Fml) (c : BitStr), fs.length = c.length → ∀ (cin : Fml) (x : ℕ → Bool),
    val (addBits fs c cin).1 x + 2 ^ fs.length * ((addBits fs c cin).2.eval x).toNat =
      val fs x + bitsVal c + (cin.eval x).toNat := by sorry
