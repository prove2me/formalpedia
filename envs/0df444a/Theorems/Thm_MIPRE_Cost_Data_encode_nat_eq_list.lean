-- Prove2me | Theorems.Thm_MIPRE_Cost_Data_encode_nat_eq_list
-- name    : MIPRE.Cost.Data.encode_nat_eq_list
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:23:05.541631+00:00
-- url     : https://prove2.me/theorems/569f148b-babc-4b0d-97d1-4dbe53b9e7c6
-- title:
--   Lemma encode_nat_eq_list of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.Repeat.Bits` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Blocks of bit strings. The repeated sampler of `thm:parallel-repetition` presents `k` copies of an input CL function on `𝔽₂^s` as one CL function on `𝔽₂^{k s}` (`CLFun.famSum`, along `finProdFinEquiv`), and its program handles vectors as bit strings cut into `k` consecutive blocks of `s` bits (`Data.chunk`). This module relates the two: the bits of a joined vector are the concatenation of the bits of its blocks (`toBits_join`), the `i`-th block of the vector read off a bit string is the vector read off the `i`-th chunk (`block_ofBits`), and likewise for indicator strings of register subspaces…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Cost
--   open MIPRE.Cost.Data
--
--   theorem MIPRE.Cost.Data.encode_nat_eq_list (n : ℕ) : (encode n : Data) = list (n.bits.map ofBool)
--   ```
--
--   **Formalization Note** `MIPRE.Cost.Data.encode_nat_eq_list` is declared in `MIPRE/Foundations/Repeat/Bits.lean`, lines 118–119. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Repeat/Bits.lean#L118-L119

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
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
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Data

theorem MIPRE.Cost.Data.encode_nat_eq_list (n : ℕ) : (encode n : Data) = list (n.bits.map ofBool) := by sorry
