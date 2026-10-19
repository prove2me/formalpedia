-- Prove2me | Theorems.Thm_MIPRE_Introspection_Honest_hideCoarseOp_aux_step_of_normalizer
-- name    : MIPRE.Introspection.Honest.hideCoarseOp_aux_step_of_normalizer
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:16:08.283422+00:00
-- url     : https://prove2.me/theorems/5c29a6bd-7c69-41b7-9eef-16e3fdc141ec
-- title:
--   The paired normalizer bound implies rigidity of the actual next coarse Hide measurement on the full seed/auxiliary carrier
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.ConditionalNormalizerStepAux` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # The next hiding step on an EPR seed with arbitrary auxiliaries
--
--   The paired normalizer bound implies rigidity of the actual next coarse
--   Hide measurement on the full seed/auxiliary carrier. All ideal mirrors and
--   conditional product identities are supplied by the honest construction.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open MIPRE.Introspection.Honest
--   open Finset Matrix Classical
--   open scoped Kronecker
--   variable {F ι A PauliAnswer H K : Type*}
--
--   theorem MIPRE.Introspection.Honest.hideCoarseOp_aux_step_of_normalizer (P : CL.CLFun F ι ℓ) (k : ℕ)
--       (hk : k + 1 < ℓ) (h : P.SupportedOn univ)
--       (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1)
--       (N : POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K))
--       (hN : IsPVM (fun a => (N.mats a).val)) {δ : ℝ}
--       (hpaired : ∑ p, snorm (registerState (ι → F) ξ)
--         (bOp (((N.map (TypedEstimates.hidingNextLater P k)).mats p).val) -
--           bOp (conditionalIdeal
--             (fun i => (aOp (hideCoarseOp P k h i) : Matrix ((ι → F) × K) _ ℂ))
--             (fun y => aOp (hidingPrefixOp P (k + 1) y))
--             (TypedEstimates.hidingNextGuarded P k) p)) ^ 2 ≤ δ) :
--       (∑ z, xSqNorm (registerState (ι → F) ξ)
--         (aOp (hideCoarseOp P (k + 1) h z) : Matrix ((ι → F) × H) _ ℂ)
--         (((N.map (TypedEstimates.hidingCoarse P (k + 1))).mats z).val)) ≤ δ
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.Honest.hideCoarseOp_aux_step_of_normalizer` is declared in `MIPRE/Foundations/Introspection/ConditionalNormalizerStepAux.lean`, lines 72–115. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ConditionalNormalizerStepAux.lean#L72-L115; blueprint lem:intro-actual-hiding-rigidity-step

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

open MIPRE
open MIPRE.Introspection
open MIPRE.Introspection.Honest
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A PauliAnswer H K : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype PauliAnswer]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem MIPRE.Introspection.Honest.hideCoarseOp_aux_step_of_normalizer (P : CL.CLFun F ι ℓ) (k : ℕ)
    (hk : k + 1 < ℓ) (h : P.SupportedOn univ)
    (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1)
    (N : POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K))
    (hN : IsPVM (fun a => (N.mats a).val)) {δ : ℝ}
    (hpaired : ∑ p, snorm (registerState (ι → F) ξ)
      (bOp (((N.map (TypedEstimates.hidingNextLater P k)).mats p).val) -
        bOp (conditionalIdeal
          (fun i => (aOp (hideCoarseOp P k h i) : Matrix ((ι → F) × K) _ ℂ))
          (fun y => aOp (hidingPrefixOp P (k + 1) y))
          (TypedEstimates.hidingNextGuarded P k) p)) ^ 2 ≤ δ) :
    (∑ z, xSqNorm (registerState (ι → F) ξ)
      (aOp (hideCoarseOp P (k + 1) h z) : Matrix ((ι → F) × H) _ ℂ)
      (((N.map (TypedEstimates.hidingCoarse P (k + 1))).mats z).val)) ≤ δ := by sorry
