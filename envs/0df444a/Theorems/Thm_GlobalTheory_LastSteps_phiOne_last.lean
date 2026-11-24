-- Prove2me | Theorems.Thm_GlobalTheory_LastSteps_phiOne_last
-- name    : GlobalTheory.LastSteps.phiOne_last
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:18.125026+00:00
-- url     : https://prove2.me/theorems/9346271c-cdc1-4025-b2b9-836f55bfb3e5
-- title:
--   Last Steps: phi One last
-- statement:
--   The Last Steps construction uses the phi One last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L427-L439
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L427-L439

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
open Classical

theorem GlobalTheory.LastSteps.phiOne_last [Fintype n] (q : Unif k) (LY : Submodule 𝒪[k] (n → k)) [LY.IsLattice k]
    (L : Submodule 𝒪[k] (n'' → k)) [L.IsLattice k] (fW : {f : Module.Dual 𝓀[k] (Red LY) // f ≠ 0})
    (x' : Matrix n'' n k) (η : n → k) :
    phiOne (ofDual LY fW) (lastPair q L) (withRow x' η) =
      latInd LY L x' * (if Lifts LY (q.1 • η) fW.1 then 1 else 0) := by sorry
