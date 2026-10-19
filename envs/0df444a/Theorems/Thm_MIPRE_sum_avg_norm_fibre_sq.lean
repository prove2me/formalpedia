-- Prove2me | Theorems.Thm_MIPRE_sum_avg_norm_fibre_sq
-- name    : MIPRE.sum_avg_norm_fibre_sq
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:42:26.641483+00:00
-- url     : https://prove2.me/theorems/eab8a434-273b-4ebd-a2d4-a8c279521d7f
-- title:
--   Parseval for a coarse-graining by a linear form. A family of vectors indexed by F_q x F_q that *sums to zero* has, on average over (alpha, beta) uniform, fibre sums under…
-- statement:
--   A statement of the module `MIPRE.Foundations.Parseval` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Parseval for the character transform. The combining stage of the Pauli appendix moves between two descriptions of the same data: an `F_q`-valued measurement `{P_a}` and its **binary observables** `O^r = sum_a (-1)^{tr(ar)} P_a`, one for each `r in F_q`. The two are Fourier transforms of each other, and what the estimates need is that the transform is an **isometry**: a bound on the observables, averaged over `r`, is a bound on the measurement elements, summed over `a`, and conversely. This file is that dictionary, for vectors and for families of matrices applied to a state: * `fourierVec` is…
--
--   **Parseval for a coarse-graining by a linear form.** A family of vectors indexed by
--   `F_q x F_q` that *sums to zero* has, on average over `(alpha, beta)` uniform, fibre sums under
--   `(a, b) |-> alpha a + beta b` whose total squared norm is `1 - 1/q` times the family's own. In
--   particular it is at most the family's: the fibres have `q` elements, and a per-fibre triangle
--   inequality would cost exactly that factor, which this avoids.
--
--   The zero-sum hypothesis is what kills the `r = 0` character; without it the statement is false
--   (take `U` supported on one point).
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix MIPRE.Weyl
--   open scoped Kronecker
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
--   variable {n : Type*} [Fintype n] [DecidableEq n]
--   variable {N : Type*} [Fintype N] [DecidableEq N]
--   variable {A : Type*} [Fintype A] [DecidableEq A]
--   variable {dA : Type*} [Fintype dA] [DecidableEq dA]
--
--   theorem MIPRE.sum_avg_norm_fibre_sq (U : F × F → (N → ℂ)) (hU : ∑ p : F × F, U p = 0) :
--       ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
--           ∑ c : F, ‖evec (∑ p ∈ univ.filter fun p : F × F =>
--             ab.1 * p.1 + ab.2 * p.2 = c, U p)‖ ^ 2
--         = (1 - (Fintype.card F : ℝ)⁻¹) * ∑ p : F × F, ‖evec (U p)‖ ^ 2
--   ```
--
--   **Formalization Note** `MIPRE.sum_avg_norm_fibre_sq` is declared in `MIPRE/Foundations/Parseval.lean`, lines 358–462. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Parseval.lean#L358-L462; blueprint lem:qld-padded-points

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval

open MIPRE
open Finset Matrix MIPRE.Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {N : Type*} [Fintype N] [DecidableEq N]
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]

theorem MIPRE.sum_avg_norm_fibre_sq (U : F × F → (N → ℂ)) (hU : ∑ p : F × F, U p = 0) :
    ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
        ∑ c : F, ‖evec (∑ p ∈ univ.filter fun p : F × F =>
          ab.1 * p.1 + ab.2 * p.2 = c, U p)‖ ^ 2
      = (1 - (Fintype.card F : ℝ)⁻¹) * ∑ p : F × F, ‖evec (U p)‖ ^ 2 := by sorry
