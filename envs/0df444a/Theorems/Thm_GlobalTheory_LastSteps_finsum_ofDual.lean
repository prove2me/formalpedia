-- Prove2me | Theorems.Thm_GlobalTheory_LastSteps_finsum_ofDual
-- name    : GlobalTheory.LastSteps.finsum_ofDual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:58.42684+00:00
-- url     : https://prove2.me/theorems/c0ae2197-2080-435a-b52a-106f8304d9c1
-- title:
--   Last Steps: finsum of Dual
-- statement:
--   The Last Steps construction uses the finsum of Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L38-L41

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

theorem GlobalTheory.LastSteps.finsum_ofDual {A : Type} [AddCommMonoid A] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (F : Pair k n → A) :
    ∑ᶠ f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}, F (ofDual L f) = ∑ P ∈ withLat L, F P := by sorry
