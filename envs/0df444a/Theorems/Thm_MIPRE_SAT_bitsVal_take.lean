-- Prove2me | Theorems.Thm_MIPRE_SAT_bitsVal_take
-- name    : MIPRE.SAT.bitsVal_take
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:26:22.724985+00:00
-- url     : https://prove2.me/theorems/8861d031-5b32-4141-94fc-347fb000c228
-- title:
--   Lemma bitsVal_take of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.FmlLib` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Formulas on bit vectors. The vocabulary in which the describer of the succinct Cook–Levin theorem is written (`planning/succinct-cook-levin.md`, S3): a *field* is a list of formulas read as a binary number, least significant bit first (`Fml.val`); the fields of an index are slices of the input bits (`Fml.field`); and the tests on fields are conjunctions and disjunctions (`andList`, `orList`), equality with a constant or another field (`eqConst`, `eqFields`), comparison (`ltConst`, `ltFields`), addition of a constant with its carry (`addBits`, `addConstRel`), subtraction of a constant by the…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.Cost
--
--   theorem MIPRE.SAT.bitsVal_take (l : BitStr) (n : ℕ) : bitsVal (l.take n) = bitsVal l % 2 ^ n
--   ```
--
--   **Formalization Note** `MIPRE.SAT.bitsVal_take` is declared in `MIPRE/Foundations/SAT/FmlLib.lean`, lines 63–82. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/FmlLib.lean#L63-L82

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
open MIPRE.Cost

theorem MIPRE.SAT.bitsVal_take (l : BitStr) (n : ℕ) : bitsVal (l.take n) = bitsVal l % 2 ^ n := by sorry
