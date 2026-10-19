-- Prove2me | Theorems.Thm_MIPRE_CL_Detyping_Program_readBits_encode
-- name    : MIPRE.CL.Detyping.Program.readBits_encode
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:10:19.63113+00:00
-- url     : https://prove2.me/theorems/e2efa7be-fd00-49e5-b402-73db3c65d27f
-- title:
--   Lemma readBits_encode of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.DetypingProgParse` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Total parsing for the detyping sampler. Raw trees are converted to canonical bit strings and binary naturals before the fixed finite graph computation. Every parser is an actual polynomial-time ambient program, including on malformed encodings.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open MIPRE.CL.Detyping
--   open MIPRE.CL.Detyping.Program
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun Polynomial
--
--   theorem MIPRE.CL.Detyping.Program.readBits_encode (l : BitStr) : readBits (encode l) = l
--   ```
--
--   **Formalization Note** `MIPRE.CL.Detyping.Program.readBits_encode` is declared in `MIPRE/Foundations/CL/DetypingProgParse.lean`, lines 46–53. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingProgParse.lean#L46-L53

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse

open MIPRE
open MIPRE.CL
open MIPRE.CL.Detyping
open MIPRE.CL.Detyping.Program
open MIPRE.Cost MIPRE.Cost.PolyTimeFun Polynomial

theorem MIPRE.CL.Detyping.Program.readBits_encode (l : BitStr) : readBits (encode l) = l := by sorry
