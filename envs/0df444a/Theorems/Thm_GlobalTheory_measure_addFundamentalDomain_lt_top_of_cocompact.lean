-- Prove2me | Theorems.Thm_GlobalTheory_measure_addFundamentalDomain_lt_top_of_cocompact
-- name    : GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:48:37.844458+00:00
-- url     : https://prove2.me/theorems/c155f5f4-2a3b-49cf-8f9e-42ca0da3ff34
-- title:
--   Global Theory: measure add Fundamental Domain lt top of cocompact
-- statement:
--   The Global Theory construction uses the measure add Fundamental Domain lt top of cocompact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MeanSquareAddFundamentalDomainOfCocompact.lean#L9-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MeanSquareAddFundamentalDomainOfCocompact.lean#L9-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MeanSquareAddFundamentalDomainOfCocompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory
open Pointwise

theorem GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact {G : Type} [AddGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
    (Γ : AddSubgroup G) [Countable Γ] {K : Set G} (hK : IsCompact K)
    (hcov : ∀ x : G, ∃ γ ∈ Γ, γ + x ∈ K) (μ : Measure G) [μ.IsAddHaarMeasure] {F : Set G}
    (hF : IsAddFundamentalDomain Γ F μ) : μ F < ⊤ := by sorry
