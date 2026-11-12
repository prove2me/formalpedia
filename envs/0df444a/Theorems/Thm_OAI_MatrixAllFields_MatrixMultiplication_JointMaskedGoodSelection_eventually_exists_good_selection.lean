-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_JointMaskedGoodSelection_eventually_exists_good_selection
-- name    : OAI.MatrixAllFields.MatrixMultiplication.JointMaskedGoodSelection.eventually_exists_good_selection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:25:50.517247+00:00
-- url     : https://prove2.me/theorems/d4887012-1f15-4ed5-9c02-d414d03c1ec2
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.JointMaskedGoodSelection.eventually_exists_good_selection (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.JointMaskedGoodSelection.eventually_exists_good_selection` of [lean/OAI/LinearAlgebra/MatrixFields/Extraction/JointMaskedGoodSelection.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Extraction/JointMaskedGoodSelection.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.JointMaskedGoodSelection`, with `open scoped BigOperators Topology Polynomial`, `open Filter JointCoarseHashing JointExtractionRates JointMaskedSelection`, `open JointOrdinarySelection (hashLevel hashSet)`, `open scoped Topology`):
--
--   ```lean
--   theorem eventually_exists_good_selection
--       {P E O V : ℕ → Type*} [∀ N, Fintype (P N)] [∀ N, Fintype (E N)]
--       (d : ∀ N, OrbitData (P N) (E N) (O N) (V N))
--       (hinj : ∀ N, Function.Injective (d N).coarse)
--       (degree : ℕ → ℕ) (B p : ℕ)
--       (heligibility : ∀ N e, ((d N).eligibilityCompetitors e).card ≤ degree N)
--       (hdegree : ∀ N e, ∀ o ∈ (d N).orbits e, ∀ v ∈ (d N).passing e o,
--         ((d N).competitors e o v).card ≤ degree N)
--       (horbits : ∀ N e, ((d N).orbits e).card ≤ B * (N + 1) ^ p)
--       {A D H : ℝ} (hH : 0 ≤ H) (hgap : D < H)
--       (hdegreeRate : ∀ η : ℝ, 0 < η →
--         ∀ᶠ N in atTop, Real.log (degree N : ℝ) / (N : ℝ) ≤ D + η)
--       (hpos : ∀ᶠ N in atTop, 0 < Fintype.card (E N))
--       (hE : Tendsto (fun N => Real.log (Fintype.card (E N) : ℝ) / (N : ℝ)) atTop (𝓝 A))
--       {ε : ℝ} (hε : 0 < ε) :
--       ∀ᶠ N in atTop, ∃ (s : Sample (P N) (hashLevel H N)) (G : Finset (E N)),
--         G.card = ⌊Real.exp ((N : ℝ) * (A - H - ε))⌋₊ ∧
--         (∀ e ∈ G, (d N).Good (hashLevel H N) (hashSet H N) (N : ℝ) e s) ∧
--         (∀ e ∈ G, ∀ f ∈ G, e ≠ f → ((d N).coarse e).1 ≠ ((d N).coarse f).1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.JointCoarseHashing.Sample`, `OAI.MatrixAllFields.MatrixMultiplication.JointCoarseHashing.Triple`, `OAI.MatrixAllFields.MatrixMultiplication.JointCoarseHashing.Word`, `OAI.MatrixAllFields.MatrixMultiplication.JointMaskedSelection.OrbitData`, `OAI.MatrixAllFields.MatrixMultiplication.JointOrdinarySelection.hashLevel`, `OAI.MatrixAllFields.MatrixMultiplication.JointOrdinarySelection.hashSet`, `OAI.MatrixAllFields.MatrixMultiplication.JointMaskedSelection.OrbitData.Good` and `OAI.MatrixAllFields.MatrixMultiplication.JointMaskedSelection.OrbitData.eligibilityCompetitors` (definitions bundle `OAIQ254M000` of this split).
--
--   **Used by.** The proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupSelection.exists_threshold_eventually_selected` of this split imports it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Extraction/JointMaskedGoodSelection.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.JointMaskedGoodSelection.eventually_exists_good_selection)

import Mathlib
import Definitions.Def_OAIQ254M000

section

attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointMaskedGoodSelection

open Filter JointCoarseHashing JointExtractionRates JointMaskedSelection
open JointOrdinarySelection (hashLevel hashSet)
open scoped Topology

attribute [local instance] Classical.propDecidable

theorem eventually_exists_good_selection
    {P E O V : ℕ → Type*} [∀ N, Fintype (P N)] [∀ N, Fintype (E N)]
    (d : ∀ N, OrbitData (P N) (E N) (O N) (V N))
    (hinj : ∀ N, Function.Injective (d N).coarse)
    (degree : ℕ → ℕ) (B p : ℕ)
    (heligibility : ∀ N e, ((d N).eligibilityCompetitors e).card ≤ degree N)
    (hdegree : ∀ N e, ∀ o ∈ (d N).orbits e, ∀ v ∈ (d N).passing e o,
      ((d N).competitors e o v).card ≤ degree N)
    (horbits : ∀ N e, ((d N).orbits e).card ≤ B * (N + 1) ^ p)
    {A D H : ℝ} (hH : 0 ≤ H) (hgap : D < H)
    (hdegreeRate : ∀ η : ℝ, 0 < η →
      ∀ᶠ N in atTop, Real.log (degree N : ℝ) / (N : ℝ) ≤ D + η)
    (hpos : ∀ᶠ N in atTop, 0 < Fintype.card (E N))
    (hE : Tendsto (fun N => Real.log (Fintype.card (E N) : ℝ) / (N : ℝ)) atTop (𝓝 A))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ (s : Sample (P N) (hashLevel H N)) (G : Finset (E N)),
      G.card = ⌊Real.exp ((N : ℝ) * (A - H - ε))⌋₊ ∧
      (∀ e ∈ G, (d N).Good (hashLevel H N) (hashSet H N) (N : ℝ) e s) ∧
      (∀ e ∈ G, ∀ f ∈ G, e ≠ f → ((d N).coarse e).1 ≠ ((d N).coarse f).1) := by
  sorry

end MatrixMultiplication.JointMaskedGoodSelection

end
end

end MatrixAllFields

end OAI
end
