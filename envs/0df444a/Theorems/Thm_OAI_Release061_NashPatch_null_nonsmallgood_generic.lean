-- Prove2me | Theorems.Thm_OAI_Release061_NashPatch_null_nonsmallgood_generic
-- name    : OAI.Release061.NashPatch.null_nonsmallgood_generic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:49:50.224994+00:00
-- url     : https://prove2.me/theorems/e0b57aff-0b7a-41dc-a191-2c72bf4b457f
-- title:
--   OAI.Release061.NashPatch.null_nonsmallgood_generic: intermediate lemma from OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Release061.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symmetry of semialgebraic bounded domains with compact quotient (result family 058)*, OpenAI Math Release, September 24, 2026, result family 58, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Release061.NashPatch.null_nonsmallgood_generic` of [lean/OAI/Analysis/SymmetricDomains/SmallSlopeGoodSupported.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/SmallSlopeGoodSupported.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Release061`, with `open Set Metric Complex`, `open scoped Topology`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped Topology ContDiff`, `open Filter`, `open scoped BigOperators Topology ContDiff`, `open Set Filter MeasureTheory`, `open scoped Topology`, `open Set Filter`, `open Set Metric`, `open scoped Topology`, `open Set Filter Metric`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter Metric`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open Set Filter Topology Metric MeasureTheory`, `open scoped Classical`):
--
--   ```lean
--   theorem NashPatch.null_nonsmallgood_generic {m N : ℕ}
--       (U V : Set (Affine N)) (hUV : U ⊆ V) (hVc : IsClosed V)
--       (hVs : IsSemialgebraic V) (hUs : IsSemialgebraic U)
--       (p : NashPatch (N+N))
--       (hp : ∀ x ∈ p.domain, p.complexMap x ∈ closure U \ U ∧
--         ∃ W : Set (Affine N), W ⊆ V ∧
--           IsOpen ((Subtype.val : V → Affine N) ⁻¹' W) ∧ p.complexMap x ∈ W ∧
--           ∃ B : Set (Affine m), IsOpen B ∧ Nonempty (Biholomorph W B)) :
--       volume {x | x ∈ p.domain ∧ m ≤ p.complexRank x ∧
--         ¬ SmallSlopeGoodNashBoundary m U V p.domain p.complexMap x} = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Release061.NashPatch`, `OAI.Release061.SmallSlopeGoodNashBoundary`, `OAI.Release061.NashPatch.complexMap` and `OAI.Release061.NashPatch.complexRank` (definitions bundle `OAIQ025S001` of this split); `OAI.Release061.Affine`, `OAI.Release061.Biholomorph` and `OAI.Release061.IsSemialgebraic` (the published bundle `Def_SymmetricDomains`).
--
--   **Used by.** The proof of `OAI.Release061.original_small_slope_good_supported_boundary` of this split imports it.
-- source:
--   OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 58; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/SmallSlopeGoodSupported.lean (declaration OAI.Release061.NashPatch.null_nonsmallgood_generic)

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology Metric MeasureTheory
open scoped Classical

theorem NashPatch.null_nonsmallgood_generic {m N : ℕ}
    (U V : Set (Affine N)) (hUV : U ⊆ V) (hVc : IsClosed V)
    (hVs : IsSemialgebraic V) (hUs : IsSemialgebraic U)
    (p : NashPatch (N+N))
    (hp : ∀ x ∈ p.domain, p.complexMap x ∈ closure U \ U ∧
      ∃ W : Set (Affine N), W ⊆ V ∧
        IsOpen ((Subtype.val : V → Affine N) ⁻¹' W) ∧ p.complexMap x ∈ W ∧
        ∃ B : Set (Affine m), IsOpen B ∧ Nonempty (Biholomorph W B)) :
    volume {x | x ∈ p.domain ∧ m ≤ p.complexRank x ∧
      ¬ SmallSlopeGoodNashBoundary m U V p.domain p.complexMap x} = 0 := by
  sorry
end

open Set Filter Topology MeasureTheory
open scoped Classical

end Release061

end

end OAI
end
