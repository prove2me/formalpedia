-- Prove2me | Theorems.Thm_GlobalTheory_LastSteps_sum_main_last
-- name    : GlobalTheory.LastSteps.sum_main_last
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:57:27.661877+00:00
-- url     : https://prove2.me/theorems/f8222feb-65df-4a33-8890-2e266b93e966
-- title:
--   Last Steps: sum main last
-- statement:
--   The Last Steps construction uses the sum main last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L454-L465
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L454-L465

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData
noncomputable section
open GlobalTheory GlobalTheory.LastSteps
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type}
variable [Fintype n] [Fintype n'] (q : Unif k) (LY : Submodule 𝒪[k] (n → k)) [LY.IsLattice k]
  (L'' : Submodule 𝒪[k] (n'' → k)) [L''.IsLattice k] {M A : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup A]
  [Module ℂ A] (x' : Matrix n'' n k) (η : n → k)

theorem GlobalTheory.LastSteps.sum_main_last (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (L : Submodule 𝒪[k] (n' → k)) (φ : Form k n' M)
    (x₀ : Matrix n n' k) :
    ∑ P ∈ withKer L, (∑ᶠ fW : {f : Module.Dual 𝓀[k] (Red LY) // f ≠ 0},
        mainDatum q χ ε P (ofDual LY fW) x₀ * (latInd LY L'' x' * cosetInd q LY fW.1 η)) • φ P =
      ∑ Q ∈ withLat LY, ∑ P' ∈ withLat L,
        (phiOne Q (lastPair q L'') (withRow x' η) * phiOne P' Q x₀) • dia ε (FFStar q χ φ) P' := by sorry
