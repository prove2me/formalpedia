-- Prove2me | Theorems.Thm_MIPRE_Introspection_legal_query_cost_le
-- name    : MIPRE.Introspection.legal_query_cost_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:10:30.500003+00:00
-- url     : https://prove2.me/theorems/a38bdb3f-de82-47db-9719-0e923a9bbccb
-- title:
--   Legal-input ambient costs fit the repaired budget with exponent five
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.Runtime` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Absolute simulation bounds on the original legal answer cut. Ambient boundedness controls input-size degree as well as a time coefficient. On four bit strings of length at most `(2^n)^λ`, the resulting absolute cost has a quadratic exponent in `λ`. The polynomial-exponent introspection budget absorbs this cost without enlarging the original game's answer alphabet. These lemmas concern actual source and universal-simulator runs. They do not yet construct the introspective decider's format checks or other subtests.
--
--   Legal-input ambient costs fit the repaired budget with exponent five.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open MIPRE.Cost
--
--   theorem MIPRE.Introspection.legal_query_cost_le {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n)
--       (x y a b : BitStr)
--       (hx : x.length ≤ (2 ^ n) ^ lam) (hy : y.length ≤ (2 ^ n) ^ lam)
--       (ha : a.length ≤ (2 ^ n) ^ lam) (hb : b.length ≤ (2 ^ n) ^ lam) :
--       (2 ^ n) ^ lam * (esize (x, y, a, b) + 1) ^ lam ≤ ansBound 5 lam n
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.legal_query_cost_le` is declared in `MIPRE/Foundations/Introspection/Runtime.lean`, lines 36–63. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/Runtime.lean#L36-L63; blueprint lem:intro-ambient-runtime

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
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
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_Introspection
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded

open MIPRE
open MIPRE.Introspection
open MIPRE.Cost

theorem MIPRE.Introspection.legal_query_cost_le {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n)
    (x y a b : BitStr)
    (hx : x.length ≤ (2 ^ n) ^ lam) (hy : y.length ≤ (2 ^ n) ^ lam)
    (ha : a.length ≤ (2 ^ n) ^ lam) (hb : b.length ≤ (2 ^ n) ^ lam) :
    (2 ^ n) ^ lam * (esize (x, y, a, b) + 1) ^ lam ≤ ansBound 5 lam n := by sorry
