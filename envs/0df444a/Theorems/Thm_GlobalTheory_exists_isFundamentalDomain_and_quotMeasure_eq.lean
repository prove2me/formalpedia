-- Prove2me | Theorems.Thm_GlobalTheory_exists_isFundamentalDomain_and_quotMeasure_eq
-- name    : GlobalTheory.exists_isFundamentalDomain_and_quotMeasure_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:17:39.504797+00:00
-- url     : https://prove2.me/theorems/a70f4a40-ede0-45f0-9513-469aa430d4d9
-- title:
--   Global Theory: exists is Fundamental Domain and quot Measure eq
-- statement:
--   The Global Theory construction uses the exists is Fundamental Domain and quot Measure eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L542-L549
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L542-L549

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Topology Filter
open scoped Pointwise ENNReal
open GlobalTheory
variable (G X : Type*) [Group G] [Countable G] [MulAction G X] [TopologicalSpace X] [T2Space X]
  [SecondCountableTopology X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ContinuousConstSMul G X]
variable {X}

theorem GlobalTheory.exists_isFundamentalDomain_and_quotMeasure_eq [ProperlyDiscontinuousSMul G X]
    (μ : Measure X) [SMulInvariantMeasure G X μ]
    (hfree : μ {x | MulAction.stabilizer G x ≠ ⊥} = 0) :
    (∃ D : Set X, MeasurableSet D ∧ IsFundamentalDomain G D μ) ∧
      ∀ D : Set X, IsFundamentalDomain G D μ →
        (μ.restrict D).map (Quotient.mk (MulAction.orbitRel G X)) = quotMeasure G μ := by sorry
