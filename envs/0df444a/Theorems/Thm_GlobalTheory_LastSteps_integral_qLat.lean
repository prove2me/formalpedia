-- Prove2me | Theorems.Thm_GlobalTheory_LastSteps_integral_qLat
-- name    : GlobalTheory.LastSteps.integral_qLat
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:56:48.442094+00:00
-- url     : https://prove2.me/theorems/ed564950-f008-430d-9898-93813b392b9b
-- title:
--   Last Steps: integral q Lat
-- statement:
--   The Last Steps construction uses the integral q Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L284-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L284-L326

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
variable [MeasurableSpace k] [BorelSpace k] (q : Unif k) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
  (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
include hψ
open Classical

theorem GlobalTheory.LastSteps.integral_qLat (η : n → k) :
    ∫ y, (if q.inv • y ∈ L then (1 : ℂ) else 0) * (ψ (η ⬝ᵥ y) : ℂ) ∂μ =
      if InDual L (q.1 • η) then (volQ μ q L : ℂ) else 0 := by sorry
