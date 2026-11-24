-- Prove2me | Theorems.Thm_GlobalTheory_LastSteps_datum_eq
-- name    : GlobalTheory.LastSteps.datum_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:57:25.835233+00:00
-- url     : https://prove2.me/theorems/9c92f6f2-429f-48c4-9867-b80b1cd130d4
-- title:
--   Last Steps: datum eq
-- statement:
--   The Last Steps construction uses the datum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L377-L394
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L377-L394

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

theorem GlobalTheory.LastSteps.datum_eq (q : Unif k) (P : Pair k n') (LY : Submodule 𝒪[k] (n → k)) (x₀ : Matrix n n' k) (y : n → k) :
    datum q P LY x₀ y = latInd (gluedS q 1 P.ker P.vec) LY (withCol x₀ y) := by sorry
