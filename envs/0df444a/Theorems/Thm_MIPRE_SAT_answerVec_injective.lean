-- Prove2me | Theorems.Thm_MIPRE_SAT_answerVec_injective
-- name    : MIPRE.SAT.answerVec_injective
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:26:09.42628+00:00
-- url     : https://prove2.me/theorems/be2f0d7c-58b7-403a-95e2-d2923cdb14fc
-- title:
--   The answer vector of a short answer determines it
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.AnswerVec` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The answer vector of a short answer determines it. `answerVec F m a` reads the tape holding `a` followed by blanks at the `2^m` positions the `m`-bit strings number. When the tape's `a` fits in the first half of those positions, `2 |a| ≤ 2^m`, the vector determines `a` (`answerVec_injective`): each cell `c < 2^{m-1}` is read off its two positions, and the cells beyond hold blanks for both strings. The soundness of answer reduction decodes the answer polynomials of a PCP proof this way.
--
--   **The answer vector of a short answer determines it.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.Cost MIPRE.LowDegree
--
--   theorem MIPRE.SAT.answerVec_injective {F : Type*} [CommRing F] [Nontrivial F] (m : ℕ) {a b : BitStr}
--       (ha : 2 * a.length ≤ 2 ^ m) (hb : 2 * b.length ≤ 2 ^ m)
--       (h : answerVec F m a = answerVec F m b) : a = b
--   ```
--
--   **Formalization Note** `MIPRE.SAT.answerVec_injective` is declared in `MIPRE/Foundations/SAT/AnswerVec.lean`, lines 42–65. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/AnswerVec.lean#L42-L65

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

open MIPRE
open MIPRE.SAT
open MIPRE.Cost MIPRE.LowDegree

theorem MIPRE.SAT.answerVec_injective {F : Type*} [CommRing F] [Nontrivial F] (m : ℕ) {a b : BitStr}
    (ha : 2 * a.length ≤ 2 ^ m) (hb : 2 * b.length ≤ 2 ^ m)
    (h : answerVec F m a = answerVec F m b) : a = b := by sorry
