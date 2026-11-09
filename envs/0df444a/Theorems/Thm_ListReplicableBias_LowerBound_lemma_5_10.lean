-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_lemma_5_10
-- name    : ListReplicableBias.LowerBound.lemma_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:57.98737+00:00
-- url     : https://prove2.me/theorems/50d18f4a-13b7-4401-af06-7f2676cf8e93
-- title:
--   Lemma 5.10 — The radius inequality
-- statement:
--   Let $0<\varepsilon,\delta<1/8$ and let $A$ be any $(d+1,\varepsilon,\delta)$-list replicable randomized adaptive algorithm drawing $N$ samples. For every $0<r\le2\varepsilon$,
--   $$\frac{16}{3}Nr^2\ge\frac{dr}{10\varepsilon}-2\ln(2(d+1)).$$
--   This is the sample-versus-radius inequality of §5.4, repeated for arbitrary algorithms in Appendix B (PDF p. 15). All parameters supplied by the surrounding source text are explicitly quantified.
--
--   Differences from the source:
--   - encoding: $\mathbb R^d$ with $\ell_\infty$ distance → functions on `Fin d` with their sup norm; reason: this reindexes the same finite coordinates and preserves every distance
--   - encoding: arbitrary randomized adaptive sampling algorithms and full histories → an arbitrary probability seed space, prefix-dependent coin choices, and the explicit transcript density; failure is `none`; reason: all private randomness is included in the seed, earlier choices are recoverable from it and earlier outcomes, and ignored tosses pad a fixed cap without changing the output law
--   - encoding: the contextual radius and source parameters → a self-contained universal statement over r in the stated interval, using Real.log; reason: the source chooses an arbitrary admissible radius, and ln denotes the natural logarithm
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Lemma 5.10, PDF p. 6 (arbitrary-transcript extension: Appendix B, PDF p. 15)

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_ListReplicability

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound

/-- Lemma 5.10, PDF p. 6, with its contextual variables bound;
Appendix B, PDF p. 15 explicitly establishes this for arbitrary algorithms. -/
theorem lemma_5_10 {d N : ℕ} (A : SamplingAlgorithm d N) (ε δ r : ℝ)
    (hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 8)) (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 8))
    (hA : IsListReplicable A (d + 1) ε δ) (hr : r ∈ Set.Ioc (0 : ℝ) (2 * ε)) :
    (d : ℝ) * r / (10 * ε) - 2 * Real.log (2 * ((d : ℝ) + 1)) ≤
      (16 / 3 : ℝ) * (N : ℝ) * r ^ 2 := by sorry

end ListReplicableBias.LowerBound
