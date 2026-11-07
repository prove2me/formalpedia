-- Prove2me | Theorems.Thm_KMeansTaper_theorem_3_3
-- name    : KMeansTaper.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:06:21.07136+00:00
-- url     : https://prove2.me/theorems/a7708444-25d5-4e31-be6e-d371a249cae9
-- title:
--   Theorem 3.3 — a deterministic polynomial-time $(1+8/e+\varepsilon)$-approximation for metric k-means
-- statement:
--   For every fixed $\varepsilon>0$, metric k-means with candidate centers admits a deterministic polynomial-time $(1+8/e+\varepsilon)$-approximation: there is a deterministic algorithm, a Turing machine (`Turing.TM2ComputableInPolyTime`, every tape alphabet finite) running in time polynomial in the input length on the published instance code (every distance in binary as sign, numerator and denominator), which on every instance (a finite rational metric, clients $J$, candidate centers $F$, $1\le k\le|F|$) returns a nonempty $S\subseteq F$ with $|S|\le k$ and
--
--   $$\sum_{j\in J}d(j,S)^2\le\Bigl(1+\frac8e+\varepsilon\Bigr)\mathrm{OPT}_k .$$
--
--   Since approximating within $1+8/e-\varepsilon$ is NP-hard (Theorem 2.1, prior work), the ratio is tight.
--
--   **Formalization Note** The shape is that of the published k-median theorem `OAI.MetricKMedian.main_finite_work` (ratio $1+2/e+\varepsilon$) with squared costs. The output is the indicator list of $S$.
--
--   Differences from the source:
--   - encoding: a deterministic polynomial-time algorithm returning S → a Turing.TM2ComputableInPolyTime machine with finite alphabets over the published encodeInstance, identity output encoding, outputting the indicator list of a nonempty S ⊆ F (CorrectRatio); reason: Lean model of deterministic polynomial time, as in OAI.MetricKMedian.main_finite_work; the empty set has infinite cost in the paper
--   - encoding: for every fixed ε > 0 → ∀ ε : ℝ, 0 < ε, before the machine; reason: ε is fixed, not an input
--   - reading: second sentence: "By Theorem 2.1 this is best possible unless P = NP" → not part of the Lean statement; reason: it restates the cited Theorem 2.1 (prior work, not proved in the paper); the printed proof "Combine Theorems 3.1 and 3.2" proves only the first sentence
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Theorem 3.3, p.4 (PDF p.7)

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_KMeansTaper_CorrectRatio

namespace KMeansTaper

open OAI.MetricKMedian (Instance encodeInstance)

/-- **Theorem 3.3 (main)**, p.4 (PDF p.7).

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3).

For every fixed `ε > 0`, metric k-means with candidate centers admits a deterministic
polynomial-time `(1 + 8/e + ε)`-approximation.

**Formalization Note.** The shape of the published `OAI.MetricKMedian.main_finite_work`
(k-median, `1 + 2/e + ε`) with squared costs: for every real `ε > 0` one
`Turing.TM2ComputableInPolyTime` machine with finite alphabets, over the published
`encodeInstance` (every distance as sign, numerator and denominator in binary), outputs on every
instance the indicator bit-list of a nonempty `S ⊆ F` with `|S| ≤ k` and
`∑_{j ∈ J} d(j, S)² ≤ (1 + 8/e + ε) OPT_k`. The theorem's second sentence ("By Theorem 2.1 this
is best possible unless P = NP") cites the hardness result of prior work and is not part of this
statement. -/
theorem theorem_3_3 : ∀ ε : ℝ, 0 < ε →
    ∃ (algorithm : Instance → List Bool)
      (M : Turing.TM2ComputableInPolyTime encodeInstance id algorithm),
      (∀ k : M.tm.K, Finite (M.tm.Γ k)) ∧
      ∀ I, CorrectRatio (1 + 8 / Real.exp 1 + ε) I (algorithm I) := by sorry

end KMeansTaper
