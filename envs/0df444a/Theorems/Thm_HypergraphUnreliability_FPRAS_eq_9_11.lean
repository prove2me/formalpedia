-- Prove2me | Theorems.Thm_HypergraphUnreliability_FPRAS_eq_9_11
-- name    : HypergraphUnreliability.FPRAS.eq_9_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:02.423487+00:00
-- url     : https://prove2.me/theorems/f6b89c64-0f1b-446c-b622-6f44640d7ab8
-- title:
--   Equation (9.11) — median of batch averages
-- statement:
--   On the connected quotient, take $S^\prime=\lceil512N/\varepsilon^2\rceil$ samples per batch and the least positive odd number $r$ of batches with $2^{-r}\le\delta$. Then the median $Z_*$ of the batch averages satisfies, with probability at least $1-\delta$ over fair bits,
--   $$|Z_*-\mu^\prime|\le\Bigl(\frac14+\frac1{512}\Bigr)\varepsilon\mu^\prime<\frac{\varepsilon\mu^\prime}{3}.$$
--
--   This is the confidence amplification of the weighted algorithm, with the paper's sample sizes.
--
--   Differences from the source: none.
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), §9.4, p. 14, and (9.11), p. 15

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_WeightedAlgorithm

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

open LabeledHypergraph

/-- (9.11), p. 15: with `S′ = ⌈512 N/ε²⌉` samples per batch and the least positive odd number `r` of
batches with `2^{-r} ≤ δ`, the median `Z_*` satisfies, with probability at least `1 - δ`,
`|Z_* - μ′| ≤ (1/4 + 1/512) ε μ′ < ε μ′ / 3`. -/
theorem eq_9_11 (D : QuotientData) (hD : D.Regular) (ε δ : ℚ) (h0 : 0 < ε) (h1 : ε < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    let P := D.params ε δ
    let μ := D.normalizedMean ε
    1 - (δ : ℝ) ≤ fairProb P.totalBits (fun ω =>
        |((P.medianOfBatches (tapeBit ω) : ℚ) : ℝ) - μ| ≤ (1 / 4 + 1 / 512) * (ε : ℝ) * μ) ∧
      (1 / 4 + 1 / 512) * (ε : ℝ) * μ < (ε : ℝ) * μ / 3 := by sorry

end HypergraphUnreliability.FPRAS
