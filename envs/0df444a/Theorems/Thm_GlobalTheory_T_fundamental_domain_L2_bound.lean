-- Prove2me | Theorems.Thm_GlobalTheory_T_fundamental_domain_L2_bound
-- name    : GlobalTheory.T.fundamental_domain_L2_bound
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:40:13.910045+00:00
-- url     : https://prove2.me/theorems/04ec317b-183b-44bc-ac0f-65b50a5baf09
-- title:
--   T: fundamental domain L2 bound
-- statement:
--   The T construction uses the fundamental domain L2 bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FundamentalDomainL2BoundStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FundamentalDomainL2BoundStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FundamentalDomainL2Bound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FundamentalDomainL2BoundStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.fundamental_domain_L2_bound : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ C : Set G, IsCompact C → ∀ n : ℝ, (∀ y : G, {γ : G | γ ∈ Γ ∧ γ * y ∈ C}.Finite ∧ (({γ : G | γ ∈ Γ ∧ γ * y ∈ C}.ncard : ℕ) : ℝ) ≤ n) → ∃ M : ℝ, ∀ F : Lp ℂ 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))), IntegrableOn (fun x => F (Quotient.mk _ x)) C μ ∧ ∫ x in C, ‖F (Quotient.mk _ x)‖ ∂μ ≤ M * ‖F‖ := by sorry
