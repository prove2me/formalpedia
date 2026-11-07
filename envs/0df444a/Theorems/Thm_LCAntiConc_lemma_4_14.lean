-- Prove2me | Theorems.Thm_LCAntiConc_lemma_4_14
-- name    : LCAntiConc.lemma_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:47:44.442214+00:00
-- url     : https://prove2.me/theorems/ede7bd5a-ddea-4d3a-a703-e0d84c66ab8a
-- title:
--   Lemma 4.14 — coefficient bound $\sum_k|b_k|\le e(m+1)^24^m$
-- statement:
--   Let $0<a\le1$, let $w$ be either of the weights $w(t)=e^{-a|t|}$ and $w(t)=e^{-at^2}$, and let $q(t)=\sum_{k=0}^mb_kt^k$ be a polynomial of degree $m$ with $q\ge0$ on $\mathbb R$ and $\int_{\mathbb R}q(t)w(t)\,dt\le1$. Then
--
--   $$\sum_{k=0}^m|b_k|\le e\,(m+1)^2\,4^m .$$
--
--   In particular there is an absolute constant $C$ such that, if $m\ge2$, then $\sum_{k=0}^m|b_k|\le m^{Cm}$.
--
--   The bound controls the coefficients of the majorants of Lemma 4.11, which the empirical version of the certificates (Lemma 5.1) needs.
--
--   Differences from the source:
--   - reading: "if m ≥ 2, then ∑|b_k| ⩽ m^{O(m)}" → ∃ C, for all a, w, q with m ≥ 2: ∑|b_k| ≤ m^{Cm}; reason: the O(·) is universal (p.27)
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Lemma 4.14, p.30 (PDF p.32)

import Mathlib

namespace LCAntiConc

open MeasureTheory

/-- **Lemma 4.14** (Coefficient bound). Let `0 < a ≤ 1`, let `w` be either of the weights
`w(t) = e^{-a|t|}` and `w(t) = e^{-at²}`, and let `q(t) = ∑_{k=0}^m b_k t^k` be a polynomial of
degree `m` with `q ≥ 0` and `∫_ℝ q(t) w(t) dt ≤ 1`. Then `∑_{k=0}^m |b_k| ≤ e(m+1)²4^m`. In
particular, if `m ≥ 2`, then `∑_{k=0}^m |b_k| ≤ m^{O(m)}`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Lemma 4.14, p.30 (PDF p.32).

**Formalization Note** `m` is `q.natDegree`. Both clauses are stated; the constant of the second
clause is absolute and comes before `a`, `w` and `q`. `m^{Cm}` is a real power. -/
theorem lemma_4_14 :
    (∀ a : ℝ, 0 < a → a ≤ 1 → ∀ w : ℝ → ℝ,
      (w = fun t => Real.exp (-a * |t|)) ∨ (w = fun t => Real.exp (-a * t ^ 2)) →
      ∀ q : Polynomial ℝ, (∀ t, 0 ≤ q.eval t) → ∫ t, q.eval t * w t ≤ 1 →
        ∑ k ∈ Finset.range (q.natDegree + 1), |q.coeff k| ≤
          Real.exp 1 * ((q.natDegree : ℝ) + 1) ^ 2 * 4 ^ q.natDegree) ∧
    ∃ C : ℝ, ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ w : ℝ → ℝ,
      (w = fun t => Real.exp (-a * |t|)) ∨ (w = fun t => Real.exp (-a * t ^ 2)) →
      ∀ q : Polynomial ℝ, (∀ t, 0 ≤ q.eval t) → ∫ t, q.eval t * w t ≤ 1 → 2 ≤ q.natDegree →
        ∑ k ∈ Finset.range (q.natDegree + 1), |q.coeff k| ≤
          (q.natDegree : ℝ) ^ (C * q.natDegree) := by sorry

end LCAntiConc
