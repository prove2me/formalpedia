-- Prove2me | Theorems.Thm_MIPRE_Introspection_isometric_valid_outcome_alice_error_le
-- name    : MIPRE.Introspection.isometric_valid_outcome_alice_error_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:41:26.083792+00:00
-- url     : https://prove2.me/theorems/964a9da4-a379-44c4-8af1-d2c51a008a5a
-- title:
--   Valid raw-answer estimates for an isometric image imply the complete mapped estimate on Alice, including the explicit malformed outcome
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.ValidOutcomeError` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Recovering all outcomes from valid-outcome extraction estimates. Pauli extraction sums only the valid full-register answers. The actual introspection induction also retains every malformed answer. Positivity and the submeasurement mass estimate extend the former guarantee to the whole mapped alphabet, without an answer-cardinality factor or a premise that malformed effects vanish.
--
--   Valid raw-answer estimates for an isometric image imply the complete
--   mapped estimate on Alice, including the explicit malformed outcome.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset Matrix Classical
--   open scoped ComplexOrder MatrixOrder
--   variable {N A B : Type*} [Fintype N] [DecidableEq N]
--   variable {H R S : Type*} [Fintype H] [DecidableEq H]
--
--   theorem MIPRE.Introspection.isometric_valid_outcome_alice_error_le (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
--       (ψ : R × S → ℂ) (hψ : ‖evec ψ‖ = 1) (M : POVM B H)
--       (f : B → Option A) (v : A → B) (hv : ∀ a, f (v a) = some a)
--       (P : Option A → Matrix R R ℂ) (hP : IsPVM P) (hPnone : P none = 0)
--       {δ : ℝ} (hclose : ∑ a, snorm ψ
--         (aOp (isometricImage V (M.mats (v a)).val - P (some a))) ^ 2 ≤ δ) :
--       (∑ a, snorm ψ (aOp (isometricImage V ((M.map f).mats a).val - P a)) ^ 2) ≤
--         2 * δ + 4 * Real.sqrt δ
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.isometric_valid_outcome_alice_error_le` is declared in `MIPRE/Foundations/Introspection/ValidOutcomeError.lean`, lines 109–130. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ValidOutcomeError.lean#L109-L130; blueprint lem:intro-valid-isometric-soundness

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
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
import Definitions.Def_MIPRE_Foundations_Introspection_IsometricStrategy

open MIPRE
open MIPRE.Introspection
open Finset Matrix Classical
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N A B : Type*} [Fintype N] [DecidableEq N]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {H R S : Type*} [Fintype H] [DecidableEq H]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]

theorem MIPRE.Introspection.isometric_valid_outcome_alice_error_le (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (ψ : R × S → ℂ) (hψ : ‖evec ψ‖ = 1) (M : POVM B H)
    (f : B → Option A) (v : A → B) (hv : ∀ a, f (v a) = some a)
    (P : Option A → Matrix R R ℂ) (hP : IsPVM P) (hPnone : P none = 0)
    {δ : ℝ} (hclose : ∑ a, snorm ψ
      (aOp (isometricImage V (M.mats (v a)).val - P (some a))) ^ 2 ≤ δ) :
    (∑ a, snorm ψ (aOp (isometricImage V ((M.map f).mats a).val - P a)) ^ 2) ≤
      2 * δ + 4 * Real.sqrt δ := by sorry
