-- Prove2me | Theorems.Thm_GlobalTheory_LastSteps_isClopen_isCompact_qLat
-- name    : GlobalTheory.LastSteps.isClopen_isCompact_qLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:44.898803+00:00
-- url     : https://prove2.me/theorems/b27babe2-e31d-4fdd-9a01-9c7ae5fddba9
-- title:
--   Last Steps: is Clopen is Compact q Lat
-- statement:
--   The Last Steps construction uses the is Clopen is Compact q Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L240-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L240-L258

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
variable [Fintype n]

theorem GlobalTheory.LastSteps.isClopen_isCompact_qLat (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] :
    IsClopen {y : n → k | q.inv • y ∈ L} ∧ IsCompact {y : n → k | q.inv • y ∈ L} := by sorry
