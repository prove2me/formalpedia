-- Prove2me | Theorems.Thm_MIPRE_Introspection_conditional_coarse_consistency
-- name    : MIPRE.Introspection.conditional_coarse_consistency
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:18:45.102453+00:00
-- url     : https://prove2.me/theorems/ce4061e3-2a85-4886-8ea0-82b50beaba99
-- title:
--   Conditional consistency for an actual pair of measurements and explicit outcome maps
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.HidingRigidity` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The conditional estimate for the actual adjacent hiding test. The earlier answer is processed using the question reported in the later answer. This is a conditional measurement, not a single fixed coarse-graining. The resulting estimate is derived from the parsed game and its actual uniform ordered-edge law, including the malformed-answer outcomes.
--
--   Conditional consistency for an actual pair of measurements and explicit
--   outcome maps. The acceptance premise is solely a scalar tested probability.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset Matrix Classical
--   open scoped Kronecker ComplexOrder MatrixOrder
--   variable {H K A B Y Z : Type*}
--
--   theorem MIPRE.Introspection.conditional_coarse_consistency (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1)
--       (M : POVM A H) (N : POVM B K) (hN : IsPVM (fun b => (N.mats b).val))
--       (f : Y → A → Z) (g : B → Y × Z) (test : A → B → Bool)
--       {δ : ℝ}
--       (hwin : 1 - δ ≤ ∑ a, ∑ b,
--         (if test a b = true then (1 : ℝ) else 0) * bornProb ψ (M.mats a).val (N.mats b).val)
--       (hcheck : ∀ a b, test a b = true → f (g b).1 a = (g b).2) :
--       conditionalCoarseDistance ψ M N f g ≤ 2 * δ
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.conditional_coarse_consistency` is declared in `MIPRE/Foundations/Introspection/HidingRigidity.lean`, lines 67–114. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/HidingRigidity.lean#L67-L114; blueprint lem:intro-adjacent-hiding

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
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
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
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
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity

open MIPRE
open MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K A B Y Z : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [Fintype B] [DecidableEq B]
  [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

theorem MIPRE.Introspection.conditional_coarse_consistency (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1)
    (M : POVM A H) (N : POVM B K) (hN : IsPVM (fun b => (N.mats b).val))
    (f : Y → A → Z) (g : B → Y × Z) (test : A → B → Bool)
    {δ : ℝ}
    (hwin : 1 - δ ≤ ∑ a, ∑ b,
      (if test a b = true then (1 : ℝ) else 0) * bornProb ψ (M.mats a).val (N.mats b).val)
    (hcheck : ∀ a b, test a b = true → f (g b).1 a = (g b).2) :
    conditionalCoarseDistance ψ M N f g ≤ 2 * δ := by sorry
