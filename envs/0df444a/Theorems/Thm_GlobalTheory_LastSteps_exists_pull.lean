-- Prove2me | Theorems.Thm_GlobalTheory_LastSteps_exists_pull
-- name    : GlobalTheory.LastSteps.exists_pull
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:58.343796+00:00
-- url     : https://prove2.me/theorems/591af671-e369-4685-a52c-b4d427385c35
-- title:
--   Last Steps: exists pull
-- statement:
--   The Last Steps construction uses the exists pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L90-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L90-L100

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
variable [Fintype n'] {L : Submodule 𝒪[k] (n' → k)} {LY : Submodule 𝒪[k] (n → k)} {x₀ : Matrix n n' k}
open Classical

theorem GlobalTheory.LastSteps.exists_pull (h : ∀ z ∈ L, x₀ *ᵥ z ∈ LY) (fW : Module.Dual 𝓀[k] (Red LY)) :
    ∃ f₀ : Module.Dual 𝓀[k] (Red L), (∀ z : L, f₀ (Red.mk L z) = fW (Red.mk LY ⟨x₀ *ᵥ z, h z z.2⟩)) ∧
      ∀ w : Module.Dual 𝓀[k] (Red L) → ℂ, ∑ᶠ f', w f' * compInd L LY f' fW x₀ = w f₀ := by sorry
