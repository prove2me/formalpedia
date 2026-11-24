-- Prove2me | Theorems.Thm_GlobalTheory_MeasurableFundamentalDomain_exists_small_open
-- name    : GlobalTheory.MeasurableFundamentalDomain.exists_small_open
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:21:23.551708+00:00
-- url     : https://prove2.me/theorems/e7b2ebb5-4057-4bf3-b961-5fe8dce83f08
-- title:
--   Measurable Fundamental Domain: exists small open
-- statement:
--   The Measurable Fundamental Domain construction uses the exists small open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMeasurableFundamentalDomain.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMeasurableFundamentalDomain.lean#L7-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMeasurableFundamentalDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MeasurableFundamentalDomain
open Set Topology

theorem GlobalTheory.MeasurableFundamentalDomain.exists_small_open {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (Γ : Subgroup G)
    (hΓ : ∀ C : Set G, IsCompact C → Set.Finite (C ∩ (↑Γ : Set G))) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ ∀ a ∈ V, ∀ b ∈ V, a * b⁻¹ ∈ Γ → a * b⁻¹ = 1 := by sorry
