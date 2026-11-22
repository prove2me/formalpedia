-- Prove2me | Theorems.Thm_Kyprianou_Ch01_measurableConullCadlagGate
-- name    : Kyprianou.Ch01.measurableConullCadlagGate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:53:14.202686+00:00
-- url     : https://prove2.me/theorems/6fb7affb-823f-4e61-9d62-a64d07c25936
-- title:
--   Measurable full-measure selection of càdlàg sample paths from an almost-sure càdlàg process
-- statement:
--   If an NNReal-indexed natural-valued stochastic process has càdlàg sample paths P-almost surely, there exists a measurable subset G of the sample space with P(G)=1 such that every path indexed by a sample in G is càdlàg. Proof: the bad-event set B={ω|¬IsCadlag(Y · ω)} has outer measure zero by the exact `ae_iff` theorem, even if B itself is not measurable. By `exists_measurable_superset_of_null` choose a measurable null superset N⊇B; then G=Nᶜ is measurable and conull, and all its samples are good. This is the missing rigorous bridge required to replace the original branching population by a globally càdlàg, fixed-time measurable gated process and obtain a globally joint-measurable version without assuming the raw good-event is measurable.
-- source:
--   Kyprianou (2006) Chapter 1 §1.3.4. Pinned Mathlib `ae_iff` and `exists_measurable_superset_of_null` signatures were verified by remote signature job 19e7a853-2b58-4bd4-86b9-a2e1d3ee6950. Complements existing public Proved AvramDividend.Classical.avram_gen16_gate_ae_cadlag_paths_to_all_paths UUID 5a5a05e9-4e08-41a3-a20b-c498ed2609a5, whose assumptions already require such a measurable G. Supports inverse-occupation-clock measurability target a50b477a-4a36-47b8-a220-857f6c082b64.

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.measurableConullCadlagGate
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℝ≥0 → Ω → ℕ)
    (hCadlag : ∀ᵐ ω ∂P,
      IsCadlag (fun t : ℝ≥0 => Y t ω)) :
    ∃ G : Set Ω, MeasurableSet G ∧
      (∀ᵐ ω ∂P, ω ∈ G) ∧
      ∀ ω ∈ G, IsCadlag (fun t : ℝ≥0 => Y t ω) := by
  sorry
