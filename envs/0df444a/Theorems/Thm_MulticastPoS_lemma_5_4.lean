-- Prove2me | Theorems.Thm_MulticastPoS_lemma_5_4
-- name    : MulticastPoS.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:53.084035+00:00
-- url     : https://prove2.me/theorems/12001571-bf91-4868-a208-fd27b16db4c1
-- title:
--   Lemma 5.4 — a numerical estimate for harmonic terms
-- statement:
--   Let $Z$ be a nonnegative integer random variable and $k$ a positive integer.
--
--   1. If $\mathbb E Z\le k$, then
--   $$
--   \mathbb E H_Z\le H_k. \tag{14}
--   $$
--   2. If $\mathbb E Z\le k$, $K\ge 4$ is an integer, $1\le k<K$, and $Z$ takes values in $\{0\}\cup\{4K,4K+1,\dots\}$, then
--   $$
--   \mathbb E H_Z\le \tfrac12 H_k. \tag{15}
--   $$
--
--   Applied to $Z=D_e$ and $k=x_e$ it gives Corollary 5.5.
--
--   **Formalization Note** $Z$ is a measurable $\mathbb N$-valued function on an arbitrary probability space and expectations are lower Lebesgue integrals with values in $[0,\infty]$; so $\mathbb EZ\le k$ needs no separate integrability hypothesis.
--
--   Differences from the source:
--   - encoding: E for a nonnegative integer random variable → ∫⁻ (lower Lebesgue integral in ℝ≥0∞) over a probability measure, Z measurable into ℕ, H_Z through ENNReal.ofReal; reason: for nonnegative integrands the lower integral is the expectation, and it is never a junk value
--   - encoding: Z takes values in {0} ∪ {4K, 4K+1, …} → ∀ ω, Z ω = 0 ∨ 4K ≤ Z ω; reason: the same condition on every outcome
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Lemma 5.4, p.12 (PDF p.13), Eqs. (14)–(15); proof Appendix D, pp.15–16

import Mathlib

open MeasureTheory

namespace MulticastPoS

/-- Lemma 5.4, a numerical estimate for harmonic terms (Huang–Yuan, *An O(log log n) Upper Bound
on the Price of Stability for Undirected Multicast Shapley Games*, STOC 2027 submission
manuscript (sha256 dd0e08d0…f6d4), p.12; proof in Appendix D, pp.15–16): let `Z` be a
nonnegative integer random variable and `k` a positive integer.

1. (14) If `E Z ≤ k`, then `E H_Z ≤ H_k`.
2. (15) If `E Z ≤ k`, `K ≥ 4` is an integer, `1 ≤ k < K`, and `Z` takes values in
   `{0} ∪ {4K, 4K + 1, …}`, then `E H_Z ≤ ½ H_k`.

**Formalization Note** `Z` is a measurable `ℕ`-valued function on a probability space;
expectations are lower Lebesgue integrals in `ℝ≥0∞` (`∫⁻`), so `E Z ≤ k` needs no separate
integrability hypothesis and cannot hold vacuously. `H_m` is Mathlib's `harmonic m` cast to `ℝ`
(nonnegative, so `ENNReal.ofReal` loses nothing). -/
theorem lemma_5_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℕ) (hZ : Measurable Z) (k : ℕ) (hk : 1 ≤ k)
    (hEZ : ∫⁻ ω, (Z ω : ENNReal) ∂μ ≤ k) :
    ∫⁻ ω, ENNReal.ofReal (harmonic (Z ω) : ℝ) ∂μ ≤ ENNReal.ofReal (harmonic k : ℝ) ∧
    ∀ K : ℕ, 4 ≤ K → k < K → (∀ ω, Z ω = 0 ∨ 4 * K ≤ Z ω) →
      ∫⁻ ω, ENNReal.ofReal (harmonic (Z ω) : ℝ) ∂μ ≤
        ENNReal.ofReal ((harmonic k : ℝ) / 2) := by sorry

end MulticastPoS
