-- Prove2me | Theorems.Thm_MIPRE_Introspection_TypedEstimates_quantumValue_ge_of_isometric_images
-- name    : MIPRE.Introspection.TypedEstimates.quantumValue_ge_of_isometric_images
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T06:47:24.019796+00:00
-- url     : https://prove2.me/theorems/bcd959db-aacc-437f-a5cb-e633e000a406
-- title:
--   The complete finite-game soundness argument with the original strategy and actual local isometries
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.IsometricSoundness` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Introspection soundness from local-isometry image estimates. This assembles the actual transported strategy and its image-complement completion. Primitive estimates can be stated on the ideal register state, as in Pauli extraction, for the image effects of the original measurements. No future normalized measurement or transported game-success assumption is required. The full projected answer alphabet includes malformed outcomes.
--
--   The complete finite-game soundness argument with the original strategy
--   and actual local isometries. Primitive image estimates and the state bound
--   are the only extraction inputs; all subsequent strategies are constructed.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open MIPRE.Introspection.TypedEstimates
--   open Finset Matrix Classical
--   variable {F ι A H K : Type u} {H₀ K₀ PauliType PauliAnswer κ : Type*}
--
--   theorem MIPRE.Introspection.TypedEstimates.quantumValue_ge_of_isometric_images
--       (E : PauliType → PauliType → Bool) (X Z : PauliType)
--       (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
--       (hL : ∀ w, (L w).ExactlyOn univ)
--       (projectPauli : PauliAnswer → ι → F)
--       (D : (ι → F) → (ι → F) → A → A → Bool)
--       (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
--         PauliAnswer → PauliAnswer → Bool)
--       (G : Game (ι → F) (ι → F) A A)
--       (hμ : ∀ x y, G.μ x y = CL.clDist (L false).eval (L true).eval x y)
--       (hD : G.D = D) (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
--       (ψ : H₀ × K₀ → ℂ) (hψ : ‖evec ψ‖ = 1)
--       (VA : Matrix ((ι → F) × H) H₀ ℂ) (VB : Matrix ((ι → F) × K) K₀ ℂ)
--       (hVA : VAᴴ * VA = 1) (hVB : VBᴴ * VB = 1)
--       (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
--         POVM (ParsedAnswer (ι → F) A PauliAnswer) H₀)
--       (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
--         POVM (ParsedAnswer (ι → F) A PauliAnswer) K₀)
--       (hMA : ∀ q, IsPVM (fun a => ((MA q).mats a).val))
--       (hMB : ∀ q, IsPVM (fun a => ((MB q).mats a).val))
--       (qX qZ : κ → ZMod 2)
--       (hqX : ∀ z, (P X).eval z = qX) (hqZ : ∀ z, (P Z).eval z = qZ)
--       {t : ℝ} (ht : 0 ≤ t)
--       (hstate : ‖evec (isometricState VA VB ψ - registerState (ι → F) ξ)‖ ^ 2 ≤ t)
--       (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB ≤ t)
--       (hX : ∑ x, stateSqNorm (registerState (ι → F) ξ)
--         (isometricImage VA
--           ((((MA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).mats x).val) -
--           (aOp (Honest.pauliXReadout x) : Matrix ((ι → F) × H) _ ℂ)) ≤ t)
--       (hZ : ∑ z, snorm (registerState (ι → F) ξ) (bOp
--         (isometricImage VB
--           ((((MB (QuestionType.pauli Z, qZ)).map (pauliProjection projectPauli)).mats z).val) -
--           (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
--             Matrix ((ι → F) × K) _ ℂ))) ^ 2 ≤ t) :
--       1 - extractedSoundnessCoefficient ℓ (TypeGraph.edges E X Z ℓ).card *
--         iteratedRoot (6 * ℓ + 1) t ≤ quantumValue G
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.TypedEstimates.quantumValue_ge_of_isometric_images` is declared in `MIPRE/Foundations/Introspection/IsometricSoundness.lean`, lines 30–145. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/IsometricSoundness.lean#L30-L145; blueprint lem:intro-valid-isometric-soundness

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
import Mathlib.Analysis.MeanInequalitiesPow
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
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
import Definitions.Def_MIPRE_Foundations_Introspection_HonestPauliRegister
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
import Definitions.Def_MIPRE_Foundations_Introspection_IsometricStrategy
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixLaw
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixConditioning
import Definitions.Def_MIPRE_Foundations_Introspection_AmbientMixing
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixMixing
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveInitialInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_AnswerRefinement
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveZFactor
import Definitions.Def_MIPRE_Foundations_Introspection_PauliAuxEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingRegister
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixAdvance
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInductionDilation
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacement
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacementRegister
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDilationTransport
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixReplacement
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveAnswerRefinement
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveAnswerDecode
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveNextFactor
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveNextInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveNextStrategy
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInduction
import Definitions.Def_MIPRE_Foundations_Introspection_HidingBaseOperators
import Definitions.Def_MIPRE_Foundations_Introspection_ProductStageZTests
import Definitions.Def_MIPRE_Foundations_Introspection_IntrospectCanonicalization
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDecodedInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveInductionInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixMarginal
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveAnswerMarginal
import Definitions.Def_MIPRE_Foundations_Introspection_ReadRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDualMarginal
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveXSplit
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDualFactor
import Definitions.Def_MIPRE_Foundations_Introspection_ProductStageReadTests
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveXTest
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveStageBudget
import Definitions.Def_MIPRE_Foundations_Introspection_RegisteredExtensionErrors
import Definitions.Def_MIPRE_Foundations_Introspection_HidingNormalizerPrefix
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidityOrientation
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidityIteration
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidityGame
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveInductionStep
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveIterationBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveInductionIteration
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePlayerSwap
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveBobIteration
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveTwoSidedIteration
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePowerBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveTerminalInvariant
import Definitions.Def_MIPRE_Foundations_Introspection_TerminalOptionExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_PrimitiveSoundness
import Definitions.Def_MIPRE_Foundations_Introspection_ExtractedStateSoundness

open MIPRE
open MIPRE.Introspection
open MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
set_option linter.unusedSectionVars false
universe u
variable {F ι A H K : Type u} {H₀ K₀ PauliType PauliAnswer κ : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [Nonempty A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype H₀] [DecidableEq H₀] [Fintype K₀] [DecidableEq K₀]
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem MIPRE.Introspection.TypedEstimates.quantumValue_ge_of_isometric_images
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (hL : ∀ w, (L w).ExactlyOn univ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (G : Game (ι → F) (ι → F) A A)
    (hμ : ∀ x y, G.μ x y = CL.clDist (L false).eval (L true).eval x y)
    (hD : G.D = D) (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (ψ : H₀ × K₀ → ℂ) (hψ : ‖evec ψ‖ = 1)
    (VA : Matrix ((ι → F) × H) H₀ ℂ) (VB : Matrix ((ι → F) × K) K₀ ℂ)
    (hVA : VAᴴ * VA = 1) (hVB : VBᴴ * VB = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) H₀)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) K₀)
    (hMA : ∀ q, IsPVM (fun a => ((MA q).mats a).val))
    (hMB : ∀ q, IsPVM (fun a => ((MB q).mats a).val))
    (qX qZ : κ → ZMod 2)
    (hqX : ∀ z, (P X).eval z = qX) (hqZ : ∀ z, (P Z).eval z = qZ)
    {t : ℝ} (ht : 0 ≤ t)
    (hstate : ‖evec (isometricState VA VB ψ - registerState (ι → F) ξ)‖ ^ 2 ≤ t)
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB ≤ t)
    (hX : ∑ x, stateSqNorm (registerState (ι → F) ξ)
      (isometricImage VA
        ((((MA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).mats x).val) -
        (aOp (Honest.pauliXReadout x) : Matrix ((ι → F) × H) _ ℂ)) ≤ t)
    (hZ : ∑ z, snorm (registerState (ι → F) ξ) (bOp
      (isometricImage VB
        ((((MB (QuestionType.pauli Z, qZ)).map (pauliProjection projectPauli)).mats z).val) -
        (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
          Matrix ((ι → F) × K) _ ℂ))) ^ 2 ≤ t) :
    1 - extractedSoundnessCoefficient ℓ (TypeGraph.edges E X Z ℓ).card *
      iteratedRoot (6 * ℓ + 1) t ≤ quantumValue G := by sorry
