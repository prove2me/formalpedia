-- Prove2me | Theorems.Thm_MIPRE_Introspection_TypedEstimates_exists_intro_iteration
-- name    : MIPRE.Introspection.TypedEstimates.exists_intro_iteration
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T06:36:13.902777+00:00
-- url     : https://prove2.me/theorems/bba08319-578b-45f1-b2be-0f2b4b9c2061
-- title:
--   A concrete projective strategy family exists after every finite Alice stage
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.AdaptiveInductionIteration` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Finite iteration of the actual Alice Introspect replacement. The auxiliary carrier and state are explicit at every level. Starting with the original projective family, each successor is constructed from the current game's tests. The numerical inverse threshold discharges every smallness premise. All other questions retain their iterated identity extensions, and all fixed hiding errors are preserved exactly.
--
--   A concrete projective strategy family exists after every finite Alice
--   stage. The original primitive bounds and explicit positive threshold suffice;
--   no future structural invariant, future error bound, or stage-smallness
--   conclusion is assumed. The full option-valued invariant includes malformed
--   answers and the support of all valid answers.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open MIPRE.Introspection.TypedEstimates
--   open Finset Matrix Classical
--   variable {H Ω : Type u} {K : Type*}
--   variable {I B : Type*} [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
--   variable {PauliType PauliAnswer κ : Type*} {F ι A : Type u}
--
--   theorem MIPRE.Introspection.TypedEstimates.exists_intro_iteration
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
--       (w : Bool) (hL : (L w).SupportedOn univ)
--       {initial η δ : ℝ} (hi0 : 0 ≤ initial) (hη0 : 0 ≤ η) (hδ0 : 0 ≤ δ)
--       (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
--         (registerState (ι → F) ξ) MA MB ≤ initial)
--       (hZ : introBobZError projectPauli Z q ξ MB ≤ η)
--       (hhide : ∀ j : Fin ℓ, hidingAliceError L w hL ξ MA j ≤ δ)
--       (hi : initial ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
--       (hη : η ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
--       (hδ : δ ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
--       (n : ℕ) (hn : n ≤ ℓ) :
--       ∃ (MN : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
--           POVM (ParsedAnswer (ι → F) A PauliAnswer)
--             ((ι → F) × introIterationAux H (Option ((ι → F) × A)) n))
--         (_ : IntroPrefixInvariant (L w) n
--           ((MN (QuestionType.introspect w, 0)).map introspectPair)),
--         (∀ t, IsPVM (fun a => ((MN t).mats a).val)) ∧
--         1 - povmValue (parsedGame E X Z P L projectPauli D DP)
--           (registerState (ι → F)
--             (introIterationState ξ (none : Option ((ι → F) × A)) n)) MN MB ≤
--               adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card η δ initial n ∧
--         (∀ t, t ≠ (QuestionType.introspect w, 0) →
--           MN t = introIterationExtend (Option ((ι → F) × A)) (MA t) n) ∧
--         (∀ j : Fin ℓ, hidingAliceError L w hL
--           (introIterationState ξ (none : Option ((ι → F) × A)) n) MN j =
--             hidingAliceError L w hL ξ MA j)
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.TypedEstimates.exists_intro_iteration` is declared in `MIPRE/Foundations/Introspection/AdaptiveInductionIteration.lean`, lines 104–198. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AdaptiveInductionIteration.lean#L104-L198; blueprint lem:intro-actual-iteration

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
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveIterationBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveInductionIteration

open MIPRE
open MIPRE.Introspection
open MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
set_option linter.unusedSectionVars false
universe u
variable {H Ω : Type u} {K : Type*}
  [Fintype H] [DecidableEq H] [Fintype Ω] [DecidableEq Ω]
  [Fintype K] [DecidableEq K]
variable {I B : Type*} [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
variable {PauliType PauliAnswer κ : Type*} {F ι A : Type u}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] {ℓ : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem MIPRE.Introspection.TypedEstimates.exists_intro_iteration
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
    (w : Bool) (hL : (L w).SupportedOn univ)
    {initial η δ : ℝ} (hi0 : 0 ≤ initial) (hη0 : 0 ≤ η) (hδ0 : 0 ≤ δ)
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ initial)
    (hZ : introBobZError projectPauli Z q ξ MB ≤ η)
    (hhide : ∀ j : Fin ℓ, hidingAliceError L w hL ξ MA j ≤ δ)
    (hi : initial ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
    (hη : η ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
    (hδ : δ ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
    (n : ℕ) (hn : n ≤ ℓ) :
    ∃ (MN : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
        POVM (ParsedAnswer (ι → F) A PauliAnswer)
          ((ι → F) × introIterationAux H (Option ((ι → F) × A)) n))
      (_ : IntroPrefixInvariant (L w) n
        ((MN (QuestionType.introspect w, 0)).map introspectPair)),
      (∀ t, IsPVM (fun a => ((MN t).mats a).val)) ∧
      1 - povmValue (parsedGame E X Z P L projectPauli D DP)
        (registerState (ι → F)
          (introIterationState ξ (none : Option ((ι → F) × A)) n)) MN MB ≤
            adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card η δ initial n ∧
      (∀ t, t ≠ (QuestionType.introspect w, 0) →
        MN t = introIterationExtend (Option ((ι → F) × A)) (MA t) n) ∧
      (∀ j : Fin ℓ, hidingAliceError L w hL
        (introIterationState ξ (none : Option ((ι → F) × A)) n) MN j =
          hidingAliceError L w hL ξ MA j) := by sorry
