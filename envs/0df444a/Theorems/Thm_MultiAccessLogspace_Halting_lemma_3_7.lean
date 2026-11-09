-- Prove2me | Theorems.Thm_MultiAccessLogspace_Halting_lemma_3_7
-- name    : MultiAccessLogspace.Halting.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:17.343822+00:00
-- url     : https://prove2.me/theorems/ebecda81-9261-4445-a709-b965287b2342
-- title:
--   Lemma 3.7 — generating hyperrulers
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $d\ge0$, $b\ge2$, and $0<\delta\le1/2$. Let $H_1,H_2,\ldots$ be measurable independent identically distributed nonnegative integer variables satisfying
--   $$
--   P(H_i\ge h)=\delta^h\qquad(0\le h\le d+1).
--   $$
--   Let the successful event assert that a first index $N$ with $H_N>d$ exists and that the list before it is a $(d,b)$-hyperruler. Then
--   $$
--   P\bigl(\text{no such first index with a hyperruler prefix exists}\bigr)\le 2\delta b^d.
--   $$
--   The event includes failure to find a first index; that has probability zero under these assumptions. This is the random-rank generation guarantee. At $d=0$ a successful prefix consists entirely of zeros.
--
--   Differences from the source:
--   - encoding: 0 ≤ d < M, with M unused in the rest of the statement → d : ℕ with no M binder; reason: every natural d has a larger M, and neither the hypotheses nor conclusion otherwise uses M
--   - encoding: H_1,H_2,…, first index N with H_N>d, and its preceding prefix → a zero-based natural sequence and an explicit existence-and-first-index event; its complement includes the null event of no first index; reason: zero-based N is the source’s N−1, avoiding truncated subtraction; no nontermination event is silently discarded
--   - encoding: i.i.d. random variables and the bound 2δ·b^d → measurable natural-valued functions on an explicit probability space, with ENNReal probabilities and ofReal of the nonnegative real bound; reason: random variables include measurability; positivity of δ and b prevents a junk conversion or a zero tail probability
-- source:
--   William M. Hoza, STOC 2027 submission #92 (October 2026), Lemma 3.7, PDF p. 8 (printed p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/92.pdf; PDF SHA-256 92de35889559d87b5a77d83317b9c7b2c8924912fbd5c712f2af3c005c8998d8

import Mathlib
import Definitions.Def_MultiAccessLogspace_Halting_Rulers

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultiAccessLogspace.Halting

/-- Lemma 3.7 (Generating hyperrulers). The sequence is indexed from `0`, so `N` here is the
source's `N - 1`: the number of entries before the first entry exceeding `d`. The event of the
statement includes the existence of that entry. -/
theorem lemma_3_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d b : ℕ) (hb : 2 ≤ b) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (H : ℕ → Ω → ℕ)
    (hmeas : ∀ i, Measurable (H i))
    (hindep : iIndepFun H P)
    (hident : ∀ i j, IdentDistrib (H i) (H j) P P)
    (htail : ∀ i h, h ≤ d + 1 → P {ω | h ≤ H i ω} = ENNReal.ofReal (δ ^ h)) :
    P {ω | ¬ ∃ N, d < H N ω ∧ (∀ i < N, H i ω ≤ d) ∧
        IsHyperruler b d ((List.range N).map fun i => H i ω)} ≤
      ENNReal.ofReal (2 * δ * (b : ℝ) ^ d) := by sorry

end MultiAccessLogspace.Halting
