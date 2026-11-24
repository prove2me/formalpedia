-- Prove2me | Theorems.Thm_GlobalTheory_LastSteps_finsum_split
-- name    : GlobalTheory.LastSteps.finsum_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:08.709093+00:00
-- url     : https://prove2.me/theorems/56a1865a-f6a1-47f5-a0fc-cdbf914b725c
-- title:
--   Last Steps: finsum split
-- statement:
--   The Last Steps construction uses the finsum split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L32-L36

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

theorem GlobalTheory.LastSteps.finsum_split {V A : Type} [Finite V] [Zero V] [AddCommMonoid A] (F : V → A) :
    ∑ᶠ v, F v = F 0 + ∑ᶠ v : {v : V // v ≠ 0}, F v := by sorry
