-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_lemma_5_6
-- name    : ListReplicableBias.LowerBound.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:41.73132+00:00
-- url     : https://prove2.me/theorems/654efd06-eecf-4fd4-bad5-3a922ac3e396
-- title:
--   Lemma 5.6 — Multiplicative change of measure, both clauses
-- statement:
--   Let $P,Q$ be the transcript laws of the same arbitrary randomized adaptive $N$-toss algorithm under $p\in[1/4,3/4]^d$ and $q\in[0,1]^d$. For every measurable transcript event $E$,
--   $$P(E)\ge Q(E)^2\exp\!\left(-\frac{16}{3}N\|p-q\|_\infty^2\right).$$
--   Moreover, for every real $r$ with $\|p-q\|_\infty\le r$,
--   $$P(E)\ge Q(E)^2\exp\!\left(-\frac{16}{3}Nr^2\right).$$
--   Both conclusions of Lemma 5.6 are retained, using the arbitrary transcript model explicitly covered by Appendix B (PDF p. 15). This transfers probabilities between nearby bias vectors.
--
--   Differences from the source:
--   - encoding: $\mathbb R^d$ with $\ell_\infty$ distance → functions on `Fin d` with their sup norm; reason: this reindexes the same finite coordinates and preserves every distance
--   - encoding: arbitrary randomized adaptive sampling algorithms and full histories → an arbitrary probability seed space, prefix-dependent coin choices, and the explicit transcript density; failure is `none`; reason: all private randomness is included in the seed, earlier choices are recoverable from it and earlier outcomes, and ignored tosses pad a fixed cap without changing the output law
--   - encoding: real event probabilities → the real value of the nonnegative transcript measure on the event; reason: valid biases make this measure a probability law, so conversion to a real number loses no mass
--   - encoding: the product measures of §5.3 and their arbitrary-transcript extension in Appendix B → one statement using the arbitrary-transcript model; reason: the product case is obtained from deterministic fixed choices, and Appendix B explicitly states that the same analysis applies
--   - generalization: fixed-allocation transcript laws in Lemma 5.6, extended in Appendix B in the list-replicable context → all randomized adaptive sampling algorithms, without a replication premise; reason: the change-of-measure estimate uses only their transcript laws and the second-moment bound; both source cases are included
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Lemma 5.6, PDF p. 5 (arbitrary-transcript extension: Appendix B, PDF p. 15)

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_ListReplicability

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound

/-- Lemma 5.6, PDF pp. 5–6, for the arbitrary algorithms of Appendix B,
PDF p. 15. Both conclusions are retained. -/
theorem lemma_5_6 {d N : ℕ} (A : SamplingAlgorithm d N)
    (p q : Fin d → ℝ) (hp : p ∈ cube d (1 / 4) (3 / 4))
    (hq : q ∈ cube d 0 1) (E : Set (A.Ω × (Fin N → Bool)))
    (hE : MeasurableSet E) :
    (transcriptLaw A q E).toReal ^ 2 *
        Real.exp (-((16 / 3 : ℝ) * (N : ℝ) * ‖p - q‖ ^ 2)) ≤
      (transcriptLaw A p E).toReal ∧
    (∀ r : ℝ, ‖p - q‖ ≤ r →
      (transcriptLaw A q E).toReal ^ 2 *
          Real.exp (-((16 / 3 : ℝ) * (N : ℝ) * r ^ 2)) ≤
        (transcriptLaw A p E).toReal) := by sorry

end ListReplicableBias.LowerBound
