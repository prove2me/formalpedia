-- Prove2me | Theorems.Thm_GlobalTheory_exists_isFundamentalDomain_of_surjective
-- name    : GlobalTheory.exists_isFundamentalDomain_of_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:57.304973+00:00
-- url     : https://prove2.me/theorems/be4ea8a4-1f4e-4b94-904c-100fe0ff9b02
-- title:
--   Global Theory: exists is Fundamental Domain of surjective
-- statement:
--   The Global Theory construction uses the exists is Fundamental Domain of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L512-L527
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L512-L527

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

theorem GlobalTheory.exists_isFundamentalDomain_of_surjective [ProperlyDiscontinuousSMul G X] {Q : Type*}
    [Group Q] [MulAction Q X] (φ : G →* Q) (hφ : Function.Surjective φ)
    (hact : ∀ g (x : X), φ g • x = g • x) (μ : Measure X)
    (hfree : ∀ g : G, φ g ≠ 1 → μ {x | g • x = x} = 0) :
    ∃ D : Set X, MeasurableSet D ∧ (∀ x, ∃ g : G, g • x ∈ D) ∧
      (∀ x ∈ D, ∀ g : G, g • x ∈ D → g • x = x) ∧ IsFundamentalDomain Q D μ := by sorry
