-- Prove2me | Theorems.Thm_MIPRE_Introspection_dilated_pvm_distance
-- name    : MIPRE.Introspection.dilated_pvm_distance
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:16:40.257924+00:00
-- url     : https://prove2.me/theorems/f1c5741d-645b-4c01-8fc4-bc3da8e4003b
-- title:
--   A fixed-state projective dilation remains close to an old PVM
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.HidingInductionDilation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Projectivizing a conditional residual measurement. One fixed ancilla is added on the residual side of every prefix. The prefix projectors are unchanged. Squared distance to the old projective measurement costs `2 sqrt(delta)`; a dilation does not in general preserve that distance.
--
--   A fixed-state projective dilation remains close to an old PVM. The bound
--   is uniform over every dilation with the displayed compression identity.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset Matrix Classical
--   open scoped Kronecker ComplexOrder MatrixOrder
--   variable {H K A T : Type*}
--
--   theorem MIPRE.Introspection.dilated_pvm_distance (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1) (a₀ : T)
--       (M R : A → Matrix H H ℂ) (P : A → Matrix (H × T) (H × T) ℂ)
--       (hM : IsPVM M) (hP : IsPVM P)
--       (hk : ∀ a, (ancillaEmbed H a₀)ᴴ * (P a * ancillaEmbed H a₀) = R a)
--       {δ : ℝ} (hd : ∑ a, stateSqNorm ψ (M a - R a) ≤ δ) :
--       (∑ a, stateSqNorm (extVecA ψ a₀) (aOp (M a) - P a)) ≤ 2 * Real.sqrt δ
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.dilated_pvm_distance` is declared in `MIPRE/Foundations/Introspection/HidingInductionDilation.lean`, lines 56–103. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/HidingInductionDilation.lean#L56-L103; blueprint lem:intro-conditional-dilation

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
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
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
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInductionDilation

open MIPRE
open MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K A T : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] [Fintype T] [DecidableEq T]

theorem MIPRE.Introspection.dilated_pvm_distance (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1) (a₀ : T)
    (M R : A → Matrix H H ℂ) (P : A → Matrix (H × T) (H × T) ℂ)
    (hM : IsPVM M) (hP : IsPVM P)
    (hk : ∀ a, (ancillaEmbed H a₀)ᴴ * (P a * ancillaEmbed H a₀) = R a)
    {δ : ℝ} (hd : ∑ a, stateSqNorm ψ (M a - R a) ≤ δ) :
    (∑ a, stateSqNorm (extVecA ψ a₀) (aOp (M a) - P a)) ≤ 2 * Real.sqrt δ := by sorry
