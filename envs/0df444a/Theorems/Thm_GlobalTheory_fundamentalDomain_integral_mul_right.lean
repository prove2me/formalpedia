-- Prove2me | Theorems.Thm_GlobalTheory_fundamentalDomain_integral_mul_right
-- name    : GlobalTheory.fundamentalDomain_integral_mul_right
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:53:35.968594+00:00
-- url     : https://prove2.me/theorems/d82d9e0c-8979-47e2-bdc6-7f69ec89a59b
-- title:
--   Global Theory: fundamental Domain integral mul right
-- statement:
--   The Global Theory construction uses the fundamental Domain integral mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FundamentalDomainIntegralMulRight.lean#L6-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FundamentalDomainIntegralMulRight.lean#L6-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FundamentalDomainIntegralMulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory

theorem GlobalTheory.fundamentalDomain_integral_mul_right {G : Type} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] (𝓕 : Set G) (f : G → ℂ) (a : G)
    (h : IsFundamentalDomain Γ 𝓕 μ) (hf : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) :
    (IntegrableOn f 𝓕 μ ↔ IntegrableOn (fun g => f (g * a)) 𝓕 μ) ∧
      ∫ g in 𝓕, f (g * a) ∂μ = ∫ g in 𝓕, f g ∂μ := by sorry
