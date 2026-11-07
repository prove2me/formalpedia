-- Prove2me | Theorems.Thm_GaussPart_lemma_3_5
-- name    : GaussPart.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:29:37.141202+00:00
-- url     : https://prove2.me/theorems/75e3781e-fa8b-48da-a7f6-f09e7b22e63d
-- title:
--   Lemma 3.5 — a moment discrepancy yields a Gaussian good split (existence part)
-- statement:
--   There are universal constants $C_0,C>1$ with the following property. Let $P=N(0,1)$, let $Q$ be a distribution on $\mathbb R$ that is $(q,\sigma)$-smooth with respect to $P$ ($q\ge1$, $\sigma\in(0,1]$), let $k\ge1$ and $\Delta\in(0,1)$, and suppose $|\mathbb E_{z\sim P}[z^i]-\mathbb E_{z\sim Q}[z^i]|\ge\Delta$ for some $i\in[k]$. Put $\Lambda=q\,(k\log(2qk)+\log(16/(\sigma\Delta)))$. Then for every $b\ge C_0\sqrt\Lambda$ there is a threshold $t\in[-b,b]$ with
--   $$\Big|\Pr_{z\sim P}[z\ge t]-\Pr_{z\sim Q}[z\ge t]\Big|\ge\frac{\Delta}{4b^k}$$
--   which is moreover a $\kappa$-Gaussian good split for $\kappa=\Delta^2/(C\Lambda)^k$.
--
--   Smoothness controls the tails of $Q$, so a low-degree moment discrepancy must show up as a tail-probability gap at a bounded threshold, and hence as a Hellinger gap between Bernoulli distributions; this is the progress measure of Algorithm 1.
--
--   **Formalization Note** The statement is `∃ C₀ C, 1 < C₀ ∧ 1 < C ∧ GoodSplitConstants C₀ C`. The algorithm part of the lemma is the companion item `GaussPart.lemma_3_5_finder`, which restates this part with the same constants.
--
--   Differences from the source:
--   - reading: "The threshold can also be chosen to be a κ-Gaussian good split" → one threshold has both the gap and the good-split property; reason: the stronger reading of "also"; the proof (p.18) gives one threshold with both
--   - encoding: universal constants C₀, C > 1 → ∃ C₀ C > 1 chosen before k, q, σ, Δ, Q (GoodSplitConstants C₀ C); reason: the same quantifier order
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Lemma 3.5, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_GaussPart_hellingerSq

open MeasureTheory ProbabilityTheory

namespace GaussPart

/-- **Lemma 3.5** (Moment Discrepancy implies a Gaussian Good Split), existence part.

arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Lemma 3.5, p.16 (PDF p.18).

"Let P = N(0, 1), and let Q be a distribution over ℝ that is (q, σ)-smooth with respect to P, where
q ≥ 1 and σ ∈ (0, 1]. Let k ∈ ℕ₊ and ∆ ∈ (0, 1), and suppose that |E_{z∼P}[z^i] − E_{z∼Q}[z^i]| ≥ ∆
for some i ∈ [k]. Define Λ := q(k log(2qk) + log(16/(σ∆))). There are universal constants C₀, C > 1
such that, for every b ≥ C₀√Λ, there exists a threshold t ∈ [−b, b] satisfying
|Pr_{z∼P}[z ≥ t] − Pr_{z∼Q}[z ≥ t]| ≥ ∆/(4b^k). The threshold can also be chosen to be a κ-Gaussian
good split, where κ := ∆²/(CΛ)^k."

**Formalization Note.** `GoodSplitConstants C₀ C` is the whole statement for given constants; the
constants come first, before `k, q, σ, ∆, Q` (they are universal). One threshold carries both
conclusions (the gap and the good split), which is the stronger reading of "can also be chosen"; the
proof on p.18 gives one threshold for both. The algorithm part ("Moreover, …") is the companion item
`GaussPart.lemma_3_5_finder`, with the same constants. -/
theorem lemma_3_5 : ∃ C₀ C : ℝ, 1 < C₀ ∧ 1 < C ∧ GoodSplitConstants C₀ C := by sorry

end GaussPart
