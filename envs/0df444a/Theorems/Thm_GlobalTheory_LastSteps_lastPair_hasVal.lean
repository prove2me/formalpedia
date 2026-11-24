-- Prove2me | Theorems.Thm_GlobalTheory_LastSteps_lastPair_hasVal
-- name    : GlobalTheory.LastSteps.lastPair_hasVal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:57:32.435523+00:00
-- url     : https://prove2.me/theorems/5bd76770-a537-4c4c-a038-78ba74c6371a
-- title:
--   Last Steps: last Pair has Val
-- statement:
--   The Last Steps construction uses the last Pair has Val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L398-L422
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L398-L422

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
variable [Fintype n']
omit [Fintype n']

theorem GlobalTheory.LastSteps.lastPair_hasVal (q : Unif k) (L : Submodule 𝒪[k] (n'' → k)) [L.IsLattice k] (v : n'' ⊕ Fin 1 → k)
    (a : 𝓀[k]) : (lastPair q L).HasVal v a ↔
      v ∘ Sum.inl ∈ L ∧ ∃ s : 𝒪[k], (s : k) = q.1 • v (Sum.inr 0) ∧ residue 𝒪[k] s = a := by sorry
