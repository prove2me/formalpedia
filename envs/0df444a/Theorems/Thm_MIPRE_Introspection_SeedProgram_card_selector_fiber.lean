-- Prove2me | Theorems.Thm_MIPRE_Introspection_SeedProgram_card_selector_fiber
-- name    : MIPRE.Introspection.SeedProgram.card_selector_fiber
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:14:31.112559+00:00
-- url     : https://prove2.me/theorems/ec32dbb1-81ed-43c0-8ef9-e0a4b9c7fdd4
-- title:
--   Every direction index occurs exactly 2^(k-j) times
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.SeedSelectorProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The executable seed enumeration for Pauli sampling. Field elements are numbered by their canonical little-endian bit strings. For `m = 2^j` and a field of size `2^k`, the selector keeps the highest `j` bits. This is the paper's equal-block selector for this explicit enumeration; it does not identify the enumeration with `Fintype.equivFin`.
--
--   Every direction index occurs exactly `2^(k-j)` times.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open MIPRE.Introspection.SeedProgram
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun MIPRE.SAT
--
--   theorem MIPRE.Introspection.SeedProgram.card_selector_fiber {k : ℕ} (E : BinField k) (j : ℕ) (hj : j ≤ k) (i : Fin (2 ^ j)) :
--       Fintype.card {a : E.carrier // selector E j hj a = i} = 2 ^ (k - j)
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.SeedProgram.card_selector_fiber` is declared in `MIPRE/Foundations/Introspection/SeedSelectorProg.lean`, lines 78–95. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/SeedSelectorProg.lean#L78-L95; blueprint lem:intro-executable-seeded-lines

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_SeedSelectorProg

open MIPRE
open MIPRE.Introspection
open MIPRE.Introspection.SeedProgram
open MIPRE.Cost MIPRE.Cost.PolyTimeFun MIPRE.SAT

theorem MIPRE.Introspection.SeedProgram.card_selector_fiber {k : ℕ} (E : BinField k) (j : ℕ) (hj : j ≤ k) (i : Fin (2 ^ j)) :
    Fintype.card {a : E.carrier // selector E j hj a = i} = 2 ^ (k - j) := by sorry
