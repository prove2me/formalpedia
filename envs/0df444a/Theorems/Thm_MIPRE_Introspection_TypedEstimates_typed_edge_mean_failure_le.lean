-- Prove2me | Theorems.Thm_MIPRE_Introspection_TypedEstimates_typed_edge_mean_failure_le
-- name    : MIPRE.Introspection.TypedEstimates.typed_edge_mean_failure_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:27:45.440904+00:00
-- url     : https://prove2.me/theorems/05a27363-db4b-4f45-a781-2e3dd7ecd876
-- title:
--   The full uniform type graph bounds the seed-averaged failure on each individual edge, without requiring injectivity of the question maps
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.PauliRestriction` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Restricting a parsed introspection strategy to its Pauli tests. Malformed outer answer constructors are completed at a fixed Pauli answer. Every originally accepted Pauli answer pair remains accepted, including on loops, where the parsed predicate checks both consistency and the Pauli rule. The uniform full type graph bounds the mean failure along each of its edges.
--
--   The full uniform type graph bounds the seed-averaged failure on each
--   individual edge, without requiring injectivity of the question maps.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open MIPRE.Introspection.TypedEstimates
--   open Finset Matrix Classical
--   variable {T F ι κ A PA H K : Type*}
--
--   theorem MIPRE.Introspection.TypedEstimates.typed_edge_mean_failure_le {B : Type*} [Fintype B]
--       (E : T → T → Bool) (X Z : T) (P : T → CL.CLFun (ZMod 2) κ 3)
--       (D : CL.Detyping.Question (QuestionType T ℓ) κ →
--         CL.Detyping.Question (QuestionType T ℓ) κ → A → B → Bool)
--       (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
--       (MA : CL.Detyping.Question (QuestionType T ℓ) κ → POVM A H)
--       (MB : CL.Detyping.Question (QuestionType T ℓ) κ → POVM B K)
--       {ε : ℝ} (hf : 1 - povmValue (TypedPresentation.game E X Z ℓ P D) ψ MA MB ≤ ε)
--       (p q : QuestionType T ℓ) (hpq : TypeGraph.Adj E X Z p q) :
--       (∑ z : κ → ZMod 2, condFail (TypedPresentation.game E X Z ℓ P D) ψ MA MB
--         (p, (TypedPresentation.family P p).eval z)
--         (q, (TypedPresentation.family P q).eval z)) / Fintype.card (κ → ZMod 2) ≤
--         (TypeGraph.edges E X Z ℓ).card * ε
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.TypedEstimates.typed_edge_mean_failure_le` is declared in `MIPRE/Foundations/Introspection/PauliRestriction.lean`, lines 105–156. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/PauliRestriction.lean#L105-L156; blueprint lem:intro-pauli-restriction

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
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
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
import Definitions.Def_MIPRE_Foundations_Introspection_PauliRestriction

open MIPRE
open MIPRE.Introspection
open MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {T F ι κ A PA H K : Type*}
  [Fintype T] [DecidableEq T] [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [Fintype PA] [DecidableEq PA]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem MIPRE.Introspection.TypedEstimates.typed_edge_mean_failure_le {B : Type*} [Fintype B]
    (E : T → T → Bool) (X Z : T) (P : T → CL.CLFun (ZMod 2) κ 3)
    (D : CL.Detyping.Question (QuestionType T ℓ) κ →
      CL.Detyping.Question (QuestionType T ℓ) κ → A → B → Bool)
    (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : CL.Detyping.Question (QuestionType T ℓ) κ → POVM A H)
    (MB : CL.Detyping.Question (QuestionType T ℓ) κ → POVM B K)
    {ε : ℝ} (hf : 1 - povmValue (TypedPresentation.game E X Z ℓ P D) ψ MA MB ≤ ε)
    (p q : QuestionType T ℓ) (hpq : TypeGraph.Adj E X Z p q) :
    (∑ z : κ → ZMod 2, condFail (TypedPresentation.game E X Z ℓ P D) ψ MA MB
      (p, (TypedPresentation.family P p).eval z)
      (q, (TypedPresentation.family P q).eval z)) / Fintype.card (κ → ZMod 2) ≤
      (TypeGraph.edges E X Z ℓ).card * ε := by sorry
