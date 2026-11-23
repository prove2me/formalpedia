-- Prove2me | Theorems.Thm_GlobalTheory_eventuallyEq_of_weierstrass_system
-- name    : GlobalTheory.eventuallyEq_of_weierstrass_system
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:28.733099+00:00
-- url     : https://prove2.me/theorems/523578d4-5183-4d1b-8a1c-ae2272c8f494
-- title:
--   Global Theory: eventually Eq of weierstrass system
-- statement:
--   The Global Theory construction uses the eventually Eq of weierstrass system property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassPAddOfNeOfDerivNeZero.lean#L75-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassPAddOfNeOfDerivNeZero.lean#L75-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair Bornology
open scoped Topology
noncomputable section
open GlobalTheory
variable (L : PeriodPair)

theorem GlobalTheory.eventuallyEq_of_weierstrass_system {f₁ g₁ f₂ g₂ : ℂ → ℂ} {k z : ℂ}
    (h₁ : ∀ᶠ w in 𝓝 z, HasDerivAt f₁ (g₁ w) w ∧ HasDerivAt g₁ (6 * f₁ w ^ 2 - k) w)
    (h₂ : ∀ᶠ w in 𝓝 z, HasDerivAt f₂ (g₂ w) w ∧ HasDerivAt g₂ (6 * f₂ w ^ 2 - k) w)
    (hf : f₁ z = f₂ z) (hg : g₁ z = g₂ z) : f₁ =ᶠ[𝓝 z] f₂ := by sorry
