-- Prove2me | Theorems.Thm_MIPRE_Introspection_exists_adaptive_prefix_dilation
-- name    : MIPRE.Introspection.exists_adaptive_prefix_dilation
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T04:05:35.182834+00:00
-- url     : https://prove2.me/theorems/dd4feaec-f4fc-4a05-9f76-c78e755e4419
-- title:
--   The one shared answer ancilla suffices although the remaining coordinate space and the next factor dimension depend on the prefix
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.AdaptivePrefixReplacement` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Actual adaptive residual projectors after mixing. Every conditioned prefix uses its actual remaining coordinates. Naimark produces projective residual measurements with the single ancilla alphabet `A` and fixed state `a₀`. The original prefix and the next Z readout remain explicit tensor factors, and the error is averaged with the actual CL law.
--
--   The one shared answer ancilla suffices although the remaining coordinate
--   space and the next factor dimension depend on the prefix.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset Matrix MIPRE.Weyl Classical
--   open scoped Kronecker
--   variable {ι F H K A : Type*} [Fintype ι] [DecidableEq ι]
--
--   theorem MIPRE.Introspection.exists_adaptive_prefix_dilation (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
--       (k : ℕ) (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1) (a₀ : A)
--       (M : (y : ι → F) → POVM ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)
--         ((stageRemaining P k y → F) × H))
--       (hM : ∀ y, IsPVM (fun p => ((M y).mats p).val))
--       {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
--       (hmarg : prefixStageMarginalError P hP k ξ (fun y p => ((M y).mats p).val) ≤ ε)
--       (hZ : prefixStageCommutatorError P hP k ξ (fun y p => ((M y).mats p).val)
--         (fun _ => wZ) (fun _ => LinearMap.id) ≤ ε)
--       (hX : prefixStageCommutatorError P hP k ξ (fun y p => ((M y).mats p).val)
--         (fun _ => wX) (fun y => CL.lperp (coordinateLinear (CLChecks.stageLinear P k y))) ≤ ε) :
--       ∃ D : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →
--         A → Matrix (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A)
--           (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A) ℂ,
--         (∀ y z, IsPVM (D y z)) ∧
--         (∑ y, prefixWeight P k y * ∑ p,
--           stateSqNorm (extVecA (registerState (stageRemaining P k y → F) ξ) a₀)
--             (aOp ((M y).mats p).val - transportedConditionalDilation (stageSplit P hP k y)
--               (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y))) (D y) p)) ≤
--           2*Real.sqrt (56*Real.sqrt ε)
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.exists_adaptive_prefix_dilation` is declared in `MIPRE/Foundations/Introspection/AdaptivePrefixReplacement.lean`, lines 125–190. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AdaptivePrefixReplacement.lean#L125-L190; blueprint lem:intro-adaptive-extraction

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
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_POVMMix_B
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_StrategyDilation
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
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixFactor
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Definitions.Def_MIPRE_Foundations_Introspection_ReadChainMaps
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveResidual
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixLaw
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixConditioning
import Definitions.Def_MIPRE_Foundations_Introspection_AmbientMixing
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixMixing
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInductionDilation
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacement
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacementRegister
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDilationTransport
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixReplacement

open MIPRE
open MIPRE.Introspection
open Finset Matrix MIPRE.Weyl Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {ι F H K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}

theorem MIPRE.Introspection.exists_adaptive_prefix_dilation (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1) (a₀ : A)
    (M : (y : ι → F) → POVM ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)
      ((stageRemaining P k y → F) × H))
    (hM : ∀ y, IsPVM (fun p => ((M y).mats p).val))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmarg : prefixStageMarginalError P hP k ξ (fun y p => ((M y).mats p).val) ≤ ε)
    (hZ : prefixStageCommutatorError P hP k ξ (fun y p => ((M y).mats p).val)
      (fun _ => wZ) (fun _ => LinearMap.id) ≤ ε)
    (hX : prefixStageCommutatorError P hP k ξ (fun y p => ((M y).mats p).val)
      (fun _ => wX) (fun y => CL.lperp (coordinateLinear (CLChecks.stageLinear P k y))) ≤ ε) :
    ∃ D : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →
      A → Matrix (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A)
        (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A) ℂ,
      (∀ y z, IsPVM (D y z)) ∧
      (∑ y, prefixWeight P k y * ∑ p,
        stateSqNorm (extVecA (registerState (stageRemaining P k y → F) ξ) a₀)
          (aOp ((M y).mats p).val - transportedConditionalDilation (stageSplit P hP k y)
            (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y))) (D y) p)) ≤
        2*Real.sqrt (56*Real.sqrt ε) := by sorry
