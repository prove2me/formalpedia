-- Prove2me | Theorems.Thm_MIPRE_Introspection_submeasurement_completion_dist_avg
-- name    : MIPRE.Introspection.submeasurement_completion_dist_avg
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:39:59.682986+00:00
-- url     : https://prove2.me/theorems/a5e9a2fb-c932-445c-a480-fe1545f5fe52
-- title:
--   Averaging preserves the completion estimate, by concavity of the square root
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.SubmeasurementCompletion` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Completing a nearby submeasurement. The paper's `lem:replace-with-measurement`, with the explicit estimate `2 δ + 4 sqrt δ` for the squared state norm. The outcome alphabet contributes no factor.
--
--   Averaging preserves the completion estimate, by concavity of the square root.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder
--   variable {N A : Type*} [Fintype N] [DecidableEq N] [Fintype A] [DecidableEq A]
--
--   theorem MIPRE.Introspection.submeasurement_completion_dist_avg {X : Type*} [Fintype X]
--       (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
--       (ψ : N → ℂ) (hψ : ‖evec ψ‖ = 1)
--       (P B C : X → A → Matrix N N ℂ) (hP : ∀ x, IsPVM (P x))
--       (hB : ∀ x a, 0 ≤ B x a) (hC : ∀ x a, 0 ≤ C x a)
--       (hCsum : ∀ x, ∑ a, C x a = 1) (hBC : ∀ x a, B x a ≤ C x a)
--       {δ : ℝ} (hclose : ∑ x, D x * ∑ a, snorm ψ (P x a - B x a) ^ 2 ≤ δ) :
--       (∑ x, D x * ∑ a, snorm ψ (P x a - C x a) ^ 2) ≤
--         2 * δ + 4 * Real.sqrt δ
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.submeasurement_completion_dist_avg` is declared in `MIPRE/Foundations/Introspection/SubmeasurementCompletion.lean`, lines 53–76. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/SubmeasurementCompletion.lean#L53-L76; blueprint lem:close-submeasurement

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
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N A : Type*} [Fintype N] [DecidableEq N] [Fintype A] [DecidableEq A]

theorem MIPRE.Introspection.submeasurement_completion_dist_avg {X : Type*} [Fintype X]
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
    (ψ : N → ℂ) (hψ : ‖evec ψ‖ = 1)
    (P B C : X → A → Matrix N N ℂ) (hP : ∀ x, IsPVM (P x))
    (hB : ∀ x a, 0 ≤ B x a) (hC : ∀ x a, 0 ≤ C x a)
    (hCsum : ∀ x, ∑ a, C x a = 1) (hBC : ∀ x a, B x a ≤ C x a)
    {δ : ℝ} (hclose : ∑ x, D x * ∑ a, snorm ψ (P x a - B x a) ^ 2 ≤ δ) :
    (∑ x, D x * ∑ a, snorm ψ (P x a - C x a) ^ 2) ≤
      2 * δ + 4 * Real.sqrt δ := by sorry
