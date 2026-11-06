-- Prove2me | Theorems.Thm_LawLocalComp_lemma_5_2
-- name    : LawLocalComp.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:10:27.491552+00:00
-- url     : https://prove2.me/theorems/a8b315eb-bd03-4393-89a9-7209d6d49a66
-- title:
--   Lemma 5.2 (A support plateau)
-- statement:
--   Let $W\ge0$ be a random variable with $\mathbb EW\le3/2$ and no support in $(a,b)$, where $0\le a<b$. Let $r,k\ge1$ be integers, let $S_1,\dots,S_k$ be independent sums of $r$ iid copies of $W$ each, and put $m_b=\mathbb E[W\mathbf 1\{W\ge b\}]$. If $b\ge2r$, then
--   $$-\frac{8k^2r}{b}\ \le\ r^{-1}\,\mathbb E\max(S_1,\dots,S_k,2r)-(2+k\,m_b)\ \le\ \frac{2ka}{r}.\tag{18}$$
--   Across a support gap the expected maximum is flat; the rank lower bound uses this to force an atom in every gap.
--
--   Differences from the source:
--   - encoding: W ≥ 0 with no support in (a, b); sums of r copies → the law μ of W is a probability measure on ℝ with μ(−∞, 0) = 0, W integrable and μ(a, b) = 0, with 0 ≤ a < b and integers r, k ≥ 1; reason: the ranges the statement presupposes; EW ≤ 3/2 is finite, so W is integrable
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Lemma 5.2, (18), p.8

import Mathlib

namespace LawLocalComp

/-- **Lemma 5.2 (A support plateau).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Lemma 5.2, (18), p.8.

Let `W ≥ 0` be a random variable of law `μ` with `EW ≤ 3/2` and no support in `(a, b)`, let
`S_1, …, S_k` be independent sums of `r` iid copies of `W` each (`kr` copies in all), and let
`m_b = E[W 1{W ≥ b}]`. If `b ≥ 2r` then
`−8k²r/b ≤ r^{−1}E max(S_1, …, S_k, 2r) − (2 + km_b) ≤ 2ka/r`.

**Formalization Note.** The page puts no finiteness on `W`, so `μ` is any probability measure on `ℝ`
with `μ(−∞, 0) = 0` and `W` integrable; a finite law is the case of finitely many atoms. "No support
in `(a, b)`" is `μ(a, b) = 0`. The `kr` copies are the product measure on `Fin k × Fin r → ℝ`. The
maximum is at most `2r + ∑ |x_{ij}|`, so it is integrable under the product and the expectation is
a genuine integral. The ranges `0 ≤ a < b`, `r ≥ 1`, `k ≥ 1` are what "no support in (a, b)" and "sums
of r copies" presuppose. -/
theorem lemma_5_2 (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ]
    (hnn : μ (Set.Iio 0) = 0) (hint : MeasureTheory.Integrable (fun w : ℝ => w) μ)
    (hW : ∫ w, w ∂μ ≤ 3 / 2) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hgap : μ (Set.Ioo a b) = 0)
    (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) (hb : 2 * (r : ℝ) ≤ b) :
    -8 * (k : ℝ) ^ 2 * r / b ≤
        (1 / (r : ℝ)) * (∫ x, max (⨆ i : Fin k, ∑ j : Fin r, x (i, j)) (2 * (r : ℝ))
            ∂(MeasureTheory.Measure.pi fun _ : Fin k × Fin r => μ)) -
          (2 + k * ∫ w in Set.Ici b, w ∂μ) ∧
      (1 / (r : ℝ)) * (∫ x, max (⨆ i : Fin k, ∑ j : Fin r, x (i, j)) (2 * (r : ℝ))
            ∂(MeasureTheory.Measure.pi fun _ : Fin k × Fin r => μ)) -
          (2 + k * ∫ w in Set.Ici b, w ∂μ) ≤ 2 * k * a / r := by sorry

end LawLocalComp
