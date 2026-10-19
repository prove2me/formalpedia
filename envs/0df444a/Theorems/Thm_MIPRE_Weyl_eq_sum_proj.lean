-- Prove2me | Theorems.Thm_MIPRE_Weyl_eq_sum_proj
-- name    : MIPRE.Weyl.eq_sum_proj
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:44:20.266623+00:00
-- url     : https://prove2.me/theorems/4be44e65-efdc-4e32-a041-a8d1d577f607
-- title:
--   A Weyl operator expands in its own projectors with the sign coefficients: the paper's eq:pauli-obs-proj for either family
-- statement:
--   A statement of the module `MIPRE.Foundations.Weyl` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Generalized Pauli operators over a field of characteristic two. The paper's `sec:generalized-pauli`: for `a ∈ F_q^n` the `X`-type operator shifts the computational basis of `(C^q)^{⊗ n}` by `a`, the `Z`-type operator is diagonal with the phase `ω^{tr(a · b)}`, and the two families *twisted-commute*, `τ^X(a) τ^Z(b) = ω^{-tr(a · b)} τ^Z(b) τ^X(a)`. This is the missing half of the Pauli basis test's infrastructure. `MIPRE/LCS/Pauli.lean` is the `2 × 2` Pauli matrices for the Magic Square; what the appendix's expansion stage and its swap isometry both run on is the `F_q` Weyl system, and that is…
--
--   **A Weyl operator expands in its own projectors** with the sign coefficients: the paper's
--   `eq:pauli-obs-proj` for either family.
--
--   The group law is *not* used: this is pure Fourier inversion on the index group, and holds for any
--   family at all. What the group law buys is that the projectors are then mutually orthogonal
--   (`proj_mul_proj`), which is what makes them a measurement.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Weyl
--   open Finset Matrix
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
--   variable {n : Type*} [Fintype n] [DecidableEq n]
--   variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
--
--   theorem MIPRE.Weyl.eq_sum_proj (a : n → F) :
--       w a = ∑ e : n → F, sgn (trDot a e) • proj w e
--   ```
--
--   **Formalization Note** `MIPRE.Weyl.eq_sum_proj` is declared in `MIPRE/Foundations/Weyl.lean`, lines 488–512. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Weyl.lean#L488-L512; blueprint def:generalized-pauli

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
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}

theorem MIPRE.Weyl.eq_sum_proj (a : n → F) :
    w a = ∑ e : n → F, sgn (trDot a e) • proj w e := by sorry
