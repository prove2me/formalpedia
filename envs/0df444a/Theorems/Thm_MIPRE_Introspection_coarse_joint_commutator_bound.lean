-- Prove2me | Theorems.Thm_MIPRE_Introspection_coarse_joint_commutator_bound
-- name    : MIPRE.Introspection.coarse_joint_commutator_bound
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T04:13:09.690196+00:00
-- url     : https://prove2.me/theorems/08749e63-20df-454c-a486-d8d0de035d90
-- title:
--   The coarse joint measurement is used directly
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.HidingInduction` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). One product-form induction step from the coarse joint measurements. The two commutators needed by Pauli mixing are derived from the tested marginals of actual projective measurements on the other party. Coarse-graining is performed before applying the commutation analysis. The error does not depend on the size of a coarse-graining fibre. The final theorem constructs the residual POVMs on `V \ U`, from averaged cross-party errors on one ambient EPR state. Identifying these measurements with the prefix-conditioned introspection strategy is a separate obligation.
--
--   The coarse joint measurement is used directly. In particular this theorem
--   does not coarse-grain an already established commutator estimate.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset Matrix MIPRE.Weyl Classical
--   open scoped Kronecker
--   variable {H K A B C O : Type*}
--
--   theorem MIPRE.Introspection.coarse_joint_commutator_bound (ψ : H × K → ℂ)
--       (M : POVM A H) (N : POVM C H) (B : POVM O K)
--       (hB : IsPVM (fun b => (B.mats b).val)) (f : O → A × C) :
--       (∑ a, ∑ c, stateSqNorm ψ
--         ((M.mats a).val * (N.mats c).val - (N.mats c).val * (M.mats a).val)) ≤
--         16 * (coarseJointLeftError ψ M B f + coarseJointRightError ψ N B f)
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.coarse_joint_commutator_bound` is declared in `MIPRE/Foundations/Introspection/HidingInduction.lean`, lines 54–74. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/HidingInduction.lean#L54-L74; blueprint lem:intro-coarse-product-stage

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Definitions.Def_MIPRE_Foundations_CL_Basic
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
import Definitions.Def_MIPRE_Foundations_Introspection_AmbientMixing
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInduction

open MIPRE
open MIPRE.Introspection
open Finset Matrix MIPRE.Weyl Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {H K A B C O : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype O] [DecidableEq O]

theorem MIPRE.Introspection.coarse_joint_commutator_bound (ψ : H × K → ℂ)
    (M : POVM A H) (N : POVM C H) (B : POVM O K)
    (hB : IsPVM (fun b => (B.mats b).val)) (f : O → A × C) :
    (∑ a, ∑ c, stateSqNorm ψ
      ((M.mats a).val * (N.mats c).val - (N.mats c).val * (M.mats a).val)) ≤
      16 * (coarseJointLeftError ψ M B f + coarseJointRightError ψ N B f) := by sorry
