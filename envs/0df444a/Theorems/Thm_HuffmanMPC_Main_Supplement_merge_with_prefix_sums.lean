-- Prove2me | Theorems.Thm_HuffmanMPC_Main_Supplement_merge_with_prefix_sums
-- name    : HuffmanMPC.Main.Supplement.merge_with_prefix_sums
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:19:44.722606+00:00
-- url     : https://prove2.me/theorems/0db70932-97b9-422d-a76a-832cd22f28a4
-- title:
--   Lemma 9.4 — sorted merge and every prefix sum; supports Theorem 9.2
-- statement:
--   There are universal constants $c>0$ and an integer $k>0$ such that, for every fixed $0<\delta<1$, one deterministic common-CRCW word program handles all original counts $m\ge2$, totals $n\ge m$, and sorted nonnegative lists $L_1,L_2$ of combined length $s\le m$ and sum at most $n$. Given the lists and their correct prefix arrays, the program returns their complete stable merge and every merged prefix sum. Equal keys follow their occurrence order in $L_1\mathbin{++}L_2$. With $\eta=\lceil m^\delta\rceil$, the same execution satisfies
--   $$\mathrm{time}\le c\delta^{-1},\qquad \mathrm{work}\le c\delta^{-1}s\eta.$$
--   Words have $k(\lfloor\log_2(2+n)\rfloor+1)$ bits. Empty lists and repeated values are permitted; the implicit empty prefix is zero. This result supports Theorem 9.2, where prefixes must remain available throughout the iteration.
--
--   Differences from the source:
--   - generalization: the Section 9 lists contain positive integer frequencies → sorted lists may also contain zeros and have sum at most the original n; reason: the rank and prefix-sum procedure applies unchanged to nonnegative keys; every source frequency list satisfies these conditions
--   - encoding: two sorted lists and their prefix sums; ties resolved by a fixed ordering → concatenation occurrence identifiers resolve ties and are returned alongside all values and nonempty prefix sums; reason: keeps multiplicities and explicitly witnesses stable occurrence order; the zero prefix is implicit, so two empty lists need zero output work
--   - reading: big-O bounds with the fixed parameter shown explicitly → positive constants c and k precede the parameter, sizes and input; reason: the explicit inverse-parameter factors and the proof estimates use uniform multipliers; no numerical multiplier is invented
--   - encoding: deterministic common-CRCW PRAM with O(log n)-bit words → finite word program, old-snapshot reads, agreeing writes, measured execution and k(floor(log2(2+n))+1)-bit words; reason: operationalizes the stated machine without aggregate or optimum instructions; parallel activation is charged per target with constant depth and no data computation
--   - encoding: asymptotic resource estimates with logarithmic factors at least one → the clamped base-two envelopes bound every admissible size; reason: changing a fixed log base changes only a uniform multiplier; bounded small cases are absorbed using the standing clamp
-- source:
--   Masoud Seddighin, Saeed Seddighin, STOC 2027 submission #377 (October 2026), Massively Parallel Algorithms for Huffman Coding, p. 45 (PDF 46), Lemma 9.4

import Definitions.Def_HuffmanMPC_Main_Supplement_Bounds

set_option autoImplicit false

namespace HuffmanMPC.Main.Supplement

/-- Lemma 9.4, p.45 (PDF 46). Both output arrays and both resource clauses;
fixed tie order, multiplicity, empty lists, and uniform word/arithmetic costs. -/
theorem merge_with_prefix_sums : ∃ (c : ℝ) (k : ℕ), 0 < c ∧ 0 < k ∧
    ∀ delta : ℝ, 0 < delta → delta < 1 → ∃ P : Program,
      MergeGuarantee P c k delta := by sorry

end HuffmanMPC.Main.Supplement
