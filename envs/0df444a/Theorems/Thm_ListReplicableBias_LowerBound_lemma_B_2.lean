-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_lemma_B_2
-- name    : ListReplicableBias.LowerBound.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:11.081435+00:00
-- url     : https://prove2.me/theorems/f90d3f71-f0b0-4365-9788-22397bd72dce
-- title:
--   Lemma B.2 — Second moment for adaptive transcript laws
-- statement:
--   Let $A$ be any randomized adaptive algorithm drawing $N$ samples, and let $P$ and $Q$ be its transcript laws under $p\in[1/4,3/4]^d$ and $q\in[0,1]^d$, respectively. Then
--   $$\int\left(\frac{dQ}{dP}\right)^2\,dP\le\exp\!\left(\frac{16}{3}N\|p-q\|_\infty^2\right).$$
--   This estimate includes continuous seed distributions and history-dependent choices. It replaces the fixed-allocation product calculation in the full-strength argument.
--
--   Differences from the source:
--   - encoding: $\mathbb R^d$ with $\ell_\infty$ distance → functions on `Fin d` with their sup norm; reason: this reindexes the same finite coordinates and preserves every distance
--   - encoding: arbitrary randomized adaptive sampling algorithms and full histories → an arbitrary probability seed space, prefix-dependent coin choices, and the explicit transcript density; failure is `none`; reason: all private randomness is included in the seed, earlier choices are recoverable from it and earlier outcomes, and ignored tosses pad a fixed cap without changing the output law
--   - encoding: expectation of a nonnegative square → the nonnegative extended-real integral of the squared Radon–Nikodym derivative; reason: this retains infinite values rather than assigning zero to a nonintegrable function; the upper bound asserts finiteness
--   - generalization: the algorithm in the surrounding Appendix B proof is list replicable → every randomized adaptive sampler, without a replication premise; reason: the second-moment calculation uses only the sampling law; the source algorithm is an instance
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Lemma B.2, PDF p. 15

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_ListReplicability

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound

/-- Lemma B.2, PDF p. 15: second moment for arbitrary adaptive randomized
transcripts. The nonnegative integral retains infinite values. -/
theorem lemma_B_2 {d N : ℕ} (A : SamplingAlgorithm d N)
    (p q : Fin d → ℝ) (hp : p ∈ cube d (1 / 4) (3 / 4))
    (hq : q ∈ cube d 0 1) :
    (∫⁻ z, ((transcriptLaw A q).rnDeriv (transcriptLaw A p) z) ^ 2
      ∂(transcriptLaw A p)) ≤
      ENNReal.ofReal (Real.exp ((16 / 3 : ℝ) * (N : ℝ) * ‖p - q‖ ^ 2)) := by sorry

end ListReplicableBias.LowerBound
