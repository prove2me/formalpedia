-- Prove2me | Theorems.Thm_MIPRE_Introspection_TypedEstimates_hidingNormalizer_estimate
-- name    : MIPRE.Introspection.TypedEstimates.hidingNormalizer_estimate
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:18:06.335962+00:00
-- url     : https://prove2.me/theorems/654e1345-1252-40ec-935a-ac4e457caa02
-- title:
--   The actual prefix chain discharges the later hiding normalizer estimate from the single Introspect-prefix estimate
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.HidingNormalizerPrefix` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # The actual hiding normalizer is the propagated question prefix
--
--   The actual prefix chain discharges the later hiding normalizer estimate
--   from the single Introspect-prefix estimate. No assumption about later hiding
--   operators or a supplied conditional marginal is needed.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open MIPRE.Introspection.TypedEstimates
--   open Finset Matrix Classical
--   variable {PauliType PauliAnswer F ι κ A H K : Type*}
--   variable [Fintype PauliType] [DecidableEq PauliType]
--
--   theorem MIPRE.Introspection.TypedEstimates.hidingNormalizer_estimate
--       (E : PauliType → PauliType → Bool) (X Z : PauliType)
--       (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
--       (projectPauli : PauliAnswer → ι → F)
--       (D : (ι → F) → (ι → F) → A → A → Bool)
--       (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
--         PauliAnswer → PauliAnswer → Bool)
--       (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
--       (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
--         POVM (ParsedAnswer (ι → F) A PauliAnswer) H)
--       (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
--         POVM (ParsedAnswer (ι → F) A PauliAnswer) K)
--       {ε δ : ℝ} (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB ≤ ε)
--       (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
--       (hL : (L w).SupportedOn univ) (Q : Option (ι → F) → Matrix K K ℂ)
--       (hintro : ∑ y, snorm ψ (bOp
--         ((((MB (QuestionType.introspect w, 0)).map
--           (reportedPrefix (L w) (k.val + 1) .introspect)).mats y).val - Q y)) ^ 2 ≤ δ) :
--       (∑ y, snorm ψ (bOp
--         (hidingNormalizer (L w) k.val (MB (QuestionType.hide w j, 0)) y - Q y)) ^ 2) ≤
--         2 * (((ℓ - j.val + 1 : ℕ) : ℝ) ^ 2 *
--           (8 * (TypeGraph.edges E X Z ℓ).card * ε)) + 2 * δ
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.TypedEstimates.hidingNormalizer_estimate` is declared in `MIPRE/Foundations/Introspection/HidingNormalizerPrefix.lean`, lines 57–96. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/HidingNormalizerPrefix.lean#L57-L96; blueprint lem:intro-actual-normalizer-prefix

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
import Definitions.Def_MIPRE_Foundations_Introspection_HidingMaps
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Definitions.Def_MIPRE_Foundations_Introspection_HidingNormalizerPrefix

open MIPRE
open MIPRE.Introspection
open MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
  [Fintype PauliAnswer] [Fintype A] [Fintype K] [DecidableEq K] {ℓ : ℕ}
variable [Fintype PauliType] [DecidableEq PauliType]
  [Fintype κ] [DecidableEq κ] [Fintype H] [DecidableEq H]

theorem MIPRE.Introspection.TypedEstimates.hidingNormalizer_estimate
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) H)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) K)
    {ε δ : ℝ} (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB ≤ ε)
    (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    (hL : (L w).SupportedOn univ) (Q : Option (ι → F) → Matrix K K ℂ)
    (hintro : ∑ y, snorm ψ (bOp
      ((((MB (QuestionType.introspect w, 0)).map
        (reportedPrefix (L w) (k.val + 1) .introspect)).mats y).val - Q y)) ^ 2 ≤ δ) :
    (∑ y, snorm ψ (bOp
      (hidingNormalizer (L w) k.val (MB (QuestionType.hide w j, 0)) y - Q y)) ^ 2) ≤
      2 * (((ℓ - j.val + 1 : ℕ) : ℝ) ^ 2 *
        (8 * (TypeGraph.edges E X Z ℓ).card * ε)) + 2 * δ := by sorry
