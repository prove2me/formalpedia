-- Prove2me | Theorems.Thm_MIPRE_Introspection_TypedEstimates_hiding_next_register_rigidity
-- name    : MIPRE.Introspection.TypedEstimates.hiding_next_register_rigidity
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:15:52.146719+00:00
-- url     : https://prove2.me/theorems/d5e2f57e-6968-4249-90d5-d00957ea726b
-- title:
--   The actual next Hide measurement is rigid with no dimension or answer alphabet factor
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.ConditionalNormalizerStepGame` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). A concrete adjacent hiding rigidity step in the actual parsed game. The state has the extracted EPR seed and an arbitrary normalized auxiliary state. Only the preceding fine estimate and the Introspect-prefix estimate are induction inputs. The actual game supplies the conditional relation and propagates the required normalizer through its hiding/Read/Introspect chain.
--
--   The actual next Hide measurement is rigid with no dimension or answer
--   alphabet factor. All ideal commutation, mirror, and accepted-answer facts are
--   proved from the construction. The remaining inputs are the preceding fine
--   rigidity and the Introspect-prefix estimate from sampling/Pauli extraction.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open MIPRE.Introspection.TypedEstimates
--   open Finset Matrix Classical MIPRE.Introspection.Honest
--   open scoped Kronecker
--   variable {PauliType PauliAnswer F ι κ A H K : Type*}
--
--   theorem MIPRE.Introspection.TypedEstimates.hiding_next_register_rigidity
--       (E : PauliType → PauliType → Bool) (X Z : PauliType)
--       (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
--       (projectPauli : PauliAnswer → ι → F)
--       (D : (ι → F) → (ι → F) → A → A → Bool)
--       (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
--         PauliAnswer → PauliAnswer → Bool)
--       (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
--       (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
--         POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H))
--       (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
--         POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K))
--       {ε δ εfine : ℝ}
--       (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
--         (registerState (ι → F) ξ) MA MB ≤ ε)
--       (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
--       (hL : (L w).SupportedOn univ)
--       (hMA : IsPVM (fun a => ((MA (QuestionType.hide w k, 0)).mats a).val))
--       (hMB : IsPVM (fun b => ((MB (QuestionType.hide w j, 0)).mats b).val))
--       (hfine : ∑ i, xSqNorm (registerState (ι → F) ξ)
--         ((((MA (QuestionType.hide w k, 0)).map (hidingCoarse (L w) k.val)).mats i).val)
--         (aOp (hideCoarseOp (L w) k.val hL i) : Matrix ((ι → F) × K) _ ℂ) ≤ εfine)
--       (hintro : ∑ y, snorm (registerState (ι → F) ξ) (bOp
--         ((((MB (QuestionType.introspect w, 0)).map
--           (reportedPrefix (L w) j.val .introspect)).mats y).val -
--             (aOp (hidingPrefixOp (L w) j.val y) : Matrix ((ι → F) × K) _ ℂ))) ^ 2 ≤ δ) :
--       (∑ z, xSqNorm (registerState (ι → F) ξ)
--         (aOp (hideCoarseOp (L w) j.val hL z) : Matrix ((ι → F) × H) _ ℂ)
--         ((((MB (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).mats z).val)) ≤
--           (6 + 48 * ((ℓ - j.val + 1 : ℕ) : ℝ) ^ 2) * (TypeGraph.edges E X Z ℓ).card * ε +
--             6 * δ + 3 * εfine
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.TypedEstimates.hiding_next_register_rigidity` is declared in `MIPRE/Foundations/Introspection/ConditionalNormalizerStepGame.lean`, lines 32–89. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ConditionalNormalizerStepGame.lean#L32-L89; blueprint lem:intro-actual-hiding-rigidity-step

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Eval.Defs
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
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
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
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCore
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizer
import Definitions.Def_MIPRE_Foundations_Introspection_HonestFirstHide
import Definitions.Def_MIPRE_Foundations_Introspection_HonestAdaptive
import Definitions.Def_MIPRE_Foundations_Introspection_HonestRead
import Definitions.Def_MIPRE_Foundations_Introspection_HonestXCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingStep
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestLabelSupport
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingChecks
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingAcceptance
import Definitions.Def_MIPRE_Foundations_Introspection_HidingMaps
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizerIdeal
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Definitions.Def_MIPRE_Foundations_Introspection_HidingNormalizerPrefix

open MIPRE
open MIPRE.Introspection
open MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical MIPRE.Introspection.Honest
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem MIPRE.Introspection.TypedEstimates.hiding_next_register_rigidity
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K))
    {ε δ εfine : ℝ}
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ ε)
    (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    (hL : (L w).SupportedOn univ)
    (hMA : IsPVM (fun a => ((MA (QuestionType.hide w k, 0)).mats a).val))
    (hMB : IsPVM (fun b => ((MB (QuestionType.hide w j, 0)).mats b).val))
    (hfine : ∑ i, xSqNorm (registerState (ι → F) ξ)
      ((((MA (QuestionType.hide w k, 0)).map (hidingCoarse (L w) k.val)).mats i).val)
      (aOp (hideCoarseOp (L w) k.val hL i) : Matrix ((ι → F) × K) _ ℂ) ≤ εfine)
    (hintro : ∑ y, snorm (registerState (ι → F) ξ) (bOp
      ((((MB (QuestionType.introspect w, 0)).map
        (reportedPrefix (L w) j.val .introspect)).mats y).val -
          (aOp (hidingPrefixOp (L w) j.val y) : Matrix ((ι → F) × K) _ ℂ))) ^ 2 ≤ δ) :
    (∑ z, xSqNorm (registerState (ι → F) ξ)
      (aOp (hideCoarseOp (L w) j.val hL z) : Matrix ((ι → F) × H) _ ℂ)
      ((((MB (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).mats z).val)) ≤
        (6 + 48 * ((ℓ - j.val + 1 : ℕ) : ℝ) ^ 2) * (TypeGraph.edges E X Z ℓ).card * ε +
          6 * δ + 3 * εfine := by sorry
