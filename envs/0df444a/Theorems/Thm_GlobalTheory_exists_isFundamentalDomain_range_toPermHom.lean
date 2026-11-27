-- Prove2me | Theorems.Thm_GlobalTheory_exists_isFundamentalDomain_range_toPermHom
-- name    : GlobalTheory.exists_isFundamentalDomain_range_toPermHom
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:22.675919+00:00
-- url     : https://prove2.me/theorems/4af87cb0-463e-4af8-bd2c-2547ac28d9e3
-- title:
--   Global Theory: exists is Fundamental Domain range to Perm Hom
-- statement:
--   The Global Theory construction uses the exists is Fundamental Domain range to Perm Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L529-L538
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L529-L538

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

theorem GlobalTheory.exists_isFundamentalDomain_range_toPermHom [ProperlyDiscontinuousSMul G X] (μ : Measure X)
    (hfree : ∀ g : G, (∃ x : X, g • x ≠ x) → μ {x | g • x = x} = 0) :
    ∃ D : Set X, MeasurableSet D ∧ (∀ x, ∃ g : G, g • x ∈ D) ∧
      (∀ x ∈ D, ∀ g : G, g • x ∈ D → g • x = x) ∧
      IsFundamentalDomain (MulAction.toPermHom G X).range D μ := by sorry
