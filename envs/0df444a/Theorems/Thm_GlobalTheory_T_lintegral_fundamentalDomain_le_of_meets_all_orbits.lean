-- Prove2me | Theorems.Thm_GlobalTheory_T_lintegral_fundamentalDomain_le_of_meets_all_orbits
-- name    : GlobalTheory.T.lintegral_fundamentalDomain_le_of_meets_all_orbits
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:35:59.601507+00:00
-- url     : https://prove2.me/theorems/0d3bfe24-d7d0-583f-bb41-08e18c4d3a45
-- title:
--   T: lintegral fundamental Domain le of meets all orbits
-- statement:
--   The T construction uses the lintegral fundamental Domain le of meets all orbits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LintegralFundamentalDomainLeOfMeetsOrbitsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LintegralFundamentalDomainLeOfMeetsOrbitsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LintegralFundamentalDomainLeOfMeetsOrbits
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LintegralFundamentalDomainLeOfMeetsOrbitsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.lintegral_fundamentalDomain_le_of_meets_all_orbits : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ] (ν : Measure G) [ν.IsMulLeftInvariant] {𝓕 S : Set G}, IsFundamentalDomain Γ 𝓕 ν → MeasurableSet S → (∀ g, ∃ γ ∈ Γ, γ * g ∈ S) → ∀ {f : G → ℝ≥0∞}, Measurable f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → ∫⁻ g in 𝓕, f g ∂ν ≤ ∫⁻ g in S, f g ∂ν := by sorry
