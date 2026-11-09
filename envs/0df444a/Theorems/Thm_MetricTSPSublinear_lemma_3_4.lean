-- Prove2me | Theorems.Thm_MetricTSPSublinear_lemma_3_4
-- name    : MetricTSPSublinear.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:23:55.573427+00:00
-- url     : https://prove2.me/theorems/e49b4914-57e7-46be-96cb-c0a3f291a132
-- title:
--   Lemma 3.4 — importance sampling with $s\ge\lceil (3B/(\varepsilon^2U))\ln(2/\delta)\rceil$ samples
-- statement:
--   Let $x_1,\dots,x_N\ge0$ and $b_1,\dots,b_N>0$ with $x_i\le b_i$. Write $X=\sum_i x_i$, $B=\sum_i b_i$, and let $U>0$ with $X\le U$. Sample indices $I_1,\dots,I_s$ independently with $\Pr[I_j=i]=p_i=b_i/B$ and set
--   $$\widehat X=\frac1s\sum_{j=1}^{s}\frac{x_{I_j}}{p_{I_j}}.$$
--   For all $\varepsilon,\delta\in(0,1)$, if $s\ge\lceil (3B/(\varepsilon^2U))\ln(2/\delta)\rceil$ then
--   $$\Pr\big[\,|\widehat X-X|>\varepsilon U\,\big]\le\delta.$$
--
--   The algorithm uses this to estimate sums of locally computable quantities (such as the cell contributions $A_P$ and $\tau_P$) from a sublinear number of evaluations.
--
--   Differences from the source:
--   - encoding: indices 1, …, n → Fin N, N = 0 allowed; reason: renamed to avoid the metric's n; for N = 0 the claim holds trivially
--   - encoding: s independent samples with Pr[I_j = i] = b_i/B → the product of s copies of the measure Σ_i (b_i/B) δ_i on Fin N; reason: the same law
--   - reading: define the unbiased estimator X̂ → X̂ is defined; unbiasedness is not stated as a conclusion; reason: the word names the estimator; the lemma's claim is the tail bound
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §3, Lemma 3.4, p.11 (PDF p.13)

import Mathlib

open MeasureTheory

namespace MetricTSPSublinear

/-- **Lemma 3.4 (Importance Sampling).**
Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §3, p.11 (PDF p.13): "Let x1, …, xn be unknown nonnegative values that can be evaluated individually, and let
b1, …, bn > 0 be known bounds satisfying xi ≤ bi. Write X = ∑_i xi and B = ∑_i bi, and let U > 0 be a known upper
bound on X. Sample s indices I1, …, Is independently, with Pr[Ij = i] = pi = bi/B, and define the unbiased estimator
X̂ = (1/s) ∑_{j=1}^{s} x_{Ij}/p_{Ij}. For any ε, δ ∈ (0, 1), taking s ≥ ⌈(3B/(ε²U)) ln(2/δ)⌉ ensures that
Pr[|X̂ − X| > εU] ≤ δ."

The indices are `Fin N` (the page's `n`). The law of `(I₁, …, I_s)` is the product of `s` copies of the categorical law
`∑_i (b_i/B) δ_i` on `Fin N`, and `X̂(I) = (1/s) ∑_j x_{I_j} / (b_{I_j}/B)`.

**Formalization Note.** The page's `n` is renamed `N`. `N = 0` is allowed; the claim holds there trivially. -/
theorem lemma_3_4 (N : ℕ) (x b : Fin N → ℝ) (hx : ∀ i, 0 ≤ x i) (hxb : ∀ i, x i ≤ b i) (hb : ∀ i, 0 < b i)
    (U : ℝ) (hU : 0 < U) (hXU : ∑ i, x i ≤ U) (ε δ : ℝ) (hε : 0 < ε ∧ ε < 1) (hδ : 0 < δ ∧ δ < 1) (s : ℕ)
    (hs : ⌈3 * (∑ i, b i) / (ε ^ 2 * U) * Real.log (2 / δ)⌉₊ ≤ s) :
    let B := ∑ i, b i
    let X := ∑ i, x i
    let cat : Measure (Fin N) := ∑ i, ENNReal.ofReal (b i / B) • Measure.dirac i
    let Xhat : (Fin s → Fin N) → ℝ := fun I => (1 / (s : ℝ)) * ∑ j, x (I j) / (b (I j) / B)
    (Measure.pi (fun _ : Fin s => cat)) {I | ε * U < |Xhat I - X|} ≤ ENNReal.ofReal δ := by sorry

end MetricTSPSublinear
