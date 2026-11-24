-- Prove2me | Theorems.Thm_GlobalTheory_LastSteps_compInd_of_not
-- name    : GlobalTheory.LastSteps.compInd_of_not
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:55.807065+00:00
-- url     : https://prove2.me/theorems/d5ece530-f749-411a-a2fe-7ffbe590289a
-- title:
--   Last Steps: comp Ind of not
-- statement:
--   The Last Steps construction uses the comp Ind of not property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L102-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L102-L103

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

theorem GlobalTheory.LastSteps.compInd_of_not (h : ¬ ∀ z ∈ L, x₀ *ᵥ z ∈ LY) (f' : Module.Dual 𝓀[k] (Red L))
    (fW : Module.Dual 𝓀[k] (Red LY)) : compInd L LY f' fW x₀ = 0 := by sorry
