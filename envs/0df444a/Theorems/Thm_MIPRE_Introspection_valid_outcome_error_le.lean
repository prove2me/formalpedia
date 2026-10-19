-- Prove2me | Theorems.Thm_MIPRE_Introspection_valid_outcome_error_le
-- name    : MIPRE.Introspection.valid_outcome_error_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:41:21.146088+00:00
-- url     : https://prove2.me/theorems/eb907690-3559-43fe-bd07-cc1ce76b0368
-- title:
--   Closeness on one correctly labelled raw answer for each valid outcome controls the complete coarse measurement, including all malformed answers
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.ValidOutcomeError` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Recovering all outcomes from valid-outcome extraction estimates. Pauli extraction sums only the valid full-register answers. The actual introspection induction also retains every malformed answer. Positivity and the submeasurement mass estimate extend the former guarantee to the whole mapped alphabet, without an answer-cardinality factor or a premise that malformed effects vanish.
--
--   Closeness on one correctly labelled raw answer for each valid outcome
--   controls the complete coarse measurement, including all malformed answers.
--   The ideal measurement has zero effect at the explicit malformed outcome.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset Matrix Classical
--   open scoped ComplexOrder MatrixOrder
--   variable {N A B : Type*} [Fintype N] [DecidableEq N]
--
--   theorem MIPRE.Introspection.valid_outcome_error_le (ψ : N → ℂ) (hψ : ‖evec ψ‖ = 1)
--       (M : B → Matrix N N ℂ) (hM : ∀ b, 0 ≤ M b) (hMsum : ∑ b, M b ≤ 1)
--       (f : B → Option A) (v : A → B) (hv : ∀ a, f (v a) = some a)
--       (P : Option A → Matrix N N ℂ) (hP : IsPVM P) (hPnone : P none = 0)
--       {δ : ℝ} (hclose : ∑ a, snorm ψ (M (v a) - P (some a)) ^ 2 ≤ δ) :
--       (∑ a, snorm ψ (fibSum M f a - P a) ^ 2) ≤ 2 * δ + 4 * Real.sqrt δ
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.valid_outcome_error_le` is declared in `MIPRE/Foundations/Introspection/ValidOutcomeError.lean`, lines 63–93. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ValidOutcomeError.lean#L63-L93; blueprint lem:intro-valid-isometric-soundness

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

theorem MIPRE.Introspection.valid_outcome_error_le (ψ : N → ℂ) (hψ : ‖evec ψ‖ = 1)
    (M : B → Matrix N N ℂ) (hM : ∀ b, 0 ≤ M b) (hMsum : ∑ b, M b ≤ 1)
    (f : B → Option A) (v : A → B) (hv : ∀ a, f (v a) = some a)
    (P : Option A → Matrix N N ℂ) (hP : IsPVM P) (hPnone : P none = 0)
    {δ : ℝ} (hclose : ∑ a, snorm ψ (M (v a) - P (some a)) ^ 2 ≤ δ) :
    (∑ a, snorm ψ (fibSum M f a - P a) ^ 2) ≤ 2 * δ + 4 * Real.sqrt δ := by sorry
