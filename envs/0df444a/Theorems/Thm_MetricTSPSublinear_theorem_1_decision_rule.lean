-- Prove2me | Theorems.Thm_MetricTSPSublinear_theorem_1_decision_rule
-- name    : MetricTSPSublinear.theorem_1_decision_rule
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:23:57.679266+00:00
-- url     : https://prove2.me/theorems/032469fd-151a-4215-8269-f3e6f899a42b
-- title:
--   Proof of Theorem 1 — the decision rule returns $\widehat{\mathrm{TSP}}\in[\mathrm{TSP},(2-\varepsilon/2)\mathrm{TSP}]$
-- statement:
--   Let $0<\varepsilon\le1$ and let $M\ge0$, $K$, $\mathrm{TSP}$, $\widehat M$, $\widehat L$ be reals with
--   1. $\max(M,2K)\le\mathrm{TSP}\le M+K$ (Claim 3.3),
--   2. $M\le\widehat M\le(1+\varepsilon/4)M$,
--   3. $0\le\widehat L\le K$, and $\widehat L\ge\frac{1+\varepsilon}2\widehat M$ whenever $D=M-K\le\varepsilon M$ (the success event of Lemma 9.1).
--
--   Return $\widehat{\mathrm{TSP}}=2\widehat M$ if $\widehat L\ge(1+\varepsilon)\widehat M/2$, and $(2-\varepsilon)\widehat M$ otherwise. Then
--   $$\mathrm{TSP}\le\widehat{\mathrm{TSP}}\le\Big(2-\frac\varepsilon2\Big)\mathrm{TSP}.$$
--
--   This is the step that turns the estimator of Lemma 9.1 into the main theorem, with $\delta=\varepsilon/2$.
--
--   Differences from the source:
--   - reading: M ≤ M̂ ≤ (1 + O(ε))M (p.9) → M ≤ M̂ ≤ (1 + ε/4)M with ε ∈ (0, 1]; reason: the page's arithmetic needs a small O(ε) constant: case 2 needs (2 − ε)(1 + cε) ≤ 2 − ε/2, true for c ≤ 1/4
--   - reading: the deduction in the proof of Theorem 1 from Claim 3.3 and the success event of Lemma 9.1 → a statement over reals M, K, TSP, M̂, L̂ with Claim 3.3's bounds, M ≥ 0 and the success event as hypotheses; reason: the paragraph is this deduction; Claim 3.3 and Lemma 9.1 are separate milestones
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, proof of Theorem 1, pp.33–34 (PDF pp.35–36)

import Mathlib

namespace MetricTSPSublinear

/-- **The decision rule of the proof of Theorem 1.**
Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), proof of Theorem 1, pp.33–34 (PDF pp.35–36): "Return T̂SP = 2M̂ if L̂ ≥ (1 + ε)M̂/2, (2 − ε)M̂ otherwise. …
On the success event of Lemma 9.1, the first case satisfies TSP ≥ 2K ≥ 2L̂ ≥ (1 + ε)M̂, so returning 2M̂ gives a ratio
below two. In the second case, the lemma implies D > εM, and hence TSP ≤ M + K = 2M − D ≤ (2 − ε)M. Both cases give
TSP ≤ T̂SP ≤ (2 − ε/2)TSP."

For reals `M, K, TSP, M̂, L̂` and `ε ∈ (0, 1]` with `M ≥ 0`, Claim 3.3 (`max(M, 2K) ≤ TSP ≤ M + K`), the estimate
`M ≤ M̂ ≤ (1 + ε/4)M`, and the success event of Lemma 9.1 (`0 ≤ L̂ ≤ K`, and `L̂ ≥ ((1+ε)/2)M̂` whenever
`D = M − K ≤ εM`), the output `T̂SP` of the rule satisfies `TSP ≤ T̂SP ≤ (2 − ε/2)TSP`.

**Formalization Note.** The page's `M ≤ M̂ ≤ (1 + O(ε))M` (p.9) is instantiated with the constant `1/4`, which makes
the page's arithmetic go through (case 2 needs `(2 − ε)(1 + c ε) ≤ 2 − ε/2`, true for `c ≤ 1/4`, `ε ≤ 1`). -/
theorem theorem_1_decision_rule (M K TSP Mhat L ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (hM : 0 ≤ M)
    (hlow : max M (2 * K) ≤ TSP) (hup : TSP ≤ M + K) (hMhat : M ≤ Mhat ∧ Mhat ≤ (1 + ε / 4) * M)
    (hL : 0 ≤ L ∧ L ≤ K) (hL2 : M - K ≤ ε * M → (1 + ε) / 2 * Mhat ≤ L) :
    let out := if (1 + ε) * Mhat / 2 ≤ L then 2 * Mhat else (2 - ε) * Mhat
    TSP ≤ out ∧ out ≤ (2 - ε / 2) * TSP := by sorry

end MetricTSPSublinear
