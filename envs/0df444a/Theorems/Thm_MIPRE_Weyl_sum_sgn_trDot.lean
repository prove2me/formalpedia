-- Prove2me | Theorems.Thm_MIPRE_Weyl_sum_sgn_trDot
-- name    : MIPRE.Weyl.sum_sgn_trDot
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:43:50.063608+00:00
-- url     : https://prove2.me/theorems/9e4b657e-51d2-4c1a-a9ea-e7f90c033ca1
-- title:
--   A nontrivial sign character sums to zero
-- statement:
--   A statement of the module `MIPRE.Foundations.Weyl` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Generalized Pauli operators over a field of characteristic two. The paper's `sec:generalized-pauli`: for `a ∈ F_q^n` the `X`-type operator shifts the computational basis of `(C^q)^{⊗ n}` by `a`, the `Z`-type operator is diagonal with the phase `ω^{tr(a · b)}`, and the two families *twisted-commute*, `τ^X(a) τ^Z(b) = ω^{-tr(a · b)} τ^Z(b) τ^X(a)`. This is the missing half of the Pauli basis test's infrastructure. `MIPRE/LCS/Pauli.lean` is the `2 × 2` Pauli matrices for the Magic Square; what the appendix's expansion stage and its swap isometry both run on is the `F_q` Weyl system, and that is…
--
--   **A nontrivial sign character sums to zero.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Weyl
--   open Finset Matrix
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
--   variable {n : Type*} [Fintype n] [DecidableEq n]
--
--   theorem MIPRE.Weyl.sum_sgn_trDot {c : n → F} (hc : c ≠ 0) :
--       ∑ a : n → F, sgn (trDot a c) = 0
--   ```
--
--   **Formalization Note** `MIPRE.Weyl.sum_sgn_trDot` is declared in `MIPRE/Foundations/Weyl.lean`, lines 289–316. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Weyl.lean#L289-L316; blueprint def:generalized-pauli

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl

open MIPRE
open MIPRE.Weyl
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem MIPRE.Weyl.sum_sgn_trDot {c : n → F} (hc : c ≠ 0) :
    ∑ a : n → F, sgn (trDot a c) = 0 := by sorry
