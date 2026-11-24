-- Prove2me | Theorems.Thm_GlobalTheory_QuotLocInt_integrableOn_compact
-- name    : GlobalTheory.QuotLocInt.integrableOn_compact
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:12:25.092533+00:00
-- url     : https://prove2.me/theorems/b28376cb-34fd-4fdf-af71-8eb4ba8fcce3
-- title:
--   Quot Loc Int: integrable On compact
-- statement:
--   The Quot Loc Int construction uses the integrable On compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FundamentalDomainL2Bound.lean#L66-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FundamentalDomainL2Bound.lean#L66-L114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FundamentalDomainL2Bound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
open GlobalTheory GlobalTheory.QuotLocInt
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant] {Γ : Subgroup G} [Countable Γ] {𝓕 : Set G}
open MeasureTheory Set
open scoped ENNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant] {Γ : Subgroup G} [Countable Γ] {𝓕 : Set G}

theorem GlobalTheory.QuotLocInt.integrableOn_compact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ]
    (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ C : Set G, IsCompact C → ∀ n : ℝ,
    (∀ y : G, {γ : G | γ ∈ Γ ∧ γ * y ∈ C}.Finite ∧
      (({γ : G | γ ∈ Γ ∧ γ * y ∈ C}.ncard : ℕ) : ℝ) ≤ n) →
    ∃ M : ℝ, ∀ F : Lp ℂ 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))),
      IntegrableOn (fun x => F (Quotient.mk _ x)) C μ ∧
        ∫ x in C, ‖F (Quotient.mk _ x)‖ ∂μ ≤ M * ‖F‖ := by sorry
