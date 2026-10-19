-- Prove2me | Theorems.Thm_MIPRE_Introspection_TypedEstimates_exists_intro_successor
-- name    : MIPRE.Introspection.TypedEstimates.exists_intro_successor
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T06:34:09.772214+00:00
-- url     : https://prove2.me/theorems/84852674-0da1-4351-b81b-6322706aa13b
-- title:
--   The actual current tests produce a projective next family and its complete prefix invariant
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.AdaptiveInductionStep` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). A successor of the actual Introspect induction. The current game's tests construct the replacement. Canonicalization and decoder recovery discharge the selected-measurement identity, and decoding gives the next structural invariant. The fixed hiding and primitive Z errors can be reused on the enlarged auxiliary space.
--
--   The actual current tests produce a projective next family and its
--   complete prefix invariant. No selected-measurement or mixing-error bound
--   is assumed: those are derived from the supplied current invariant.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open MIPRE.Introspection.TypedEstimates
--   open Finset Matrix Classical MIPRE.Weyl
--   variable {PauliType PauliAnswer F ι κ A H K : Type*}
--
--   theorem MIPRE.Introspection.TypedEstimates.exists_intro_successor
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
--       (hMA : ∀ q, IsPVM (fun a => ((MA q).mats a).val))
--       (hMB : ∀ q, IsPVM (fun a => ((MB q).mats a).val))
--       (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q)
--       (w : Bool) (hL : (L w).SupportedOn univ) (j : Fin ℓ)
--       (I : IntroPrefixInvariant (L w) j.val
--         ((MA (QuestionType.introspect w, 0)).map introspectPair))
--       {ε η δ : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
--       (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
--         (registerState (ι → F) ξ) MA MB ≤ ε)
--       (hZ : introBobZError projectPauli Z q ξ MB ≤ η)
--       (hhide : hidingAliceError L w hL ξ MA j ≤ δ)
--       (hsmall : adaptiveStageBudget (ℓ - j.val)
--         ((TypeGraph.edges E X Z ℓ).card * ε) η δ ≤ 1) :
--       ∃ (MA' : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
--           POVM (ParsedAnswer (ι → F) A PauliAnswer)
--             ((ι → F) × (H × Option ((ι → F) × A))))
--         (_ : IntroPrefixInvariant (L w) (j.val + 1)
--           ((MA' (QuestionType.introspect w, 0)).map introspectPair)),
--         (∀ t, IsPVM (fun a => ((MA' t).mats a).val)) ∧
--         1 - povmValue (parsedGame E X Z P L projectPauli D DP)
--           (registerState (ι → F) (extVecA ξ (none : Option ((ι → F) × A)))) MA' MB ≤
--             ε + adaptiveStepLoss (adaptiveStageBudget (ℓ - j.val)
--               ((TypeGraph.edges E X Z ℓ).card * ε) η δ) ∧
--         (∀ t, t ≠ (QuestionType.introspect w, 0) → MA' t = registeredExtendPOVM (MA t)) ∧
--         (∀ i : Fin ℓ, hidingAliceError L w hL
--           (extVecA ξ (none : Option ((ι → F) × A))) MA' i = hidingAliceError L w hL ξ MA i)
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.TypedEstimates.exists_intro_successor` is declared in `MIPRE/Foundations/Introspection/AdaptiveInductionStep.lean`, lines 88–166. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AdaptiveInductionStep.lean#L88-L166; blueprint lem:intro-actual-successor

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

open MIPRE
open MIPRE.Introspection
open MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical MIPRE.Weyl
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] {ℓ : ℕ}
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem MIPRE.Introspection.TypedEstimates.exists_intro_successor
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
    (hMA : ∀ q, IsPVM (fun a => ((MA q).mats a).val))
    (hMB : ∀ q, IsPVM (fun a => ((MB q).mats a).val))
    (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q)
    (w : Bool) (hL : (L w).SupportedOn univ) (j : Fin ℓ)
    (I : IntroPrefixInvariant (L w) j.val
      ((MA (QuestionType.introspect w, 0)).map introspectPair))
    {ε η δ : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ ε)
    (hZ : introBobZError projectPauli Z q ξ MB ≤ η)
    (hhide : hidingAliceError L w hL ξ MA j ≤ δ)
    (hsmall : adaptiveStageBudget (ℓ - j.val)
      ((TypeGraph.edges E X Z ℓ).card * ε) η δ ≤ 1) :
    ∃ (MA' : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
        POVM (ParsedAnswer (ι → F) A PauliAnswer)
          ((ι → F) × (H × Option ((ι → F) × A))))
      (_ : IntroPrefixInvariant (L w) (j.val + 1)
        ((MA' (QuestionType.introspect w, 0)).map introspectPair)),
      (∀ t, IsPVM (fun a => ((MA' t).mats a).val)) ∧
      1 - povmValue (parsedGame E X Z P L projectPauli D DP)
        (registerState (ι → F) (extVecA ξ (none : Option ((ι → F) × A)))) MA' MB ≤
          ε + adaptiveStepLoss (adaptiveStageBudget (ℓ - j.val)
            ((TypeGraph.edges E X Z ℓ).card * ε) η δ) ∧
      (∀ t, t ≠ (QuestionType.introspect w, 0) → MA' t = registeredExtendPOVM (MA t)) ∧
      (∀ i : Fin ℓ, hidingAliceError L w hL
        (extVecA ξ (none : Option ((ι → F) × A))) MA' i = hidingAliceError L w hL ξ MA i) := by sorry
