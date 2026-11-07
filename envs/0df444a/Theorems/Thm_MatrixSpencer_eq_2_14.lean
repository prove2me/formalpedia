-- Prove2me | Theorems.Thm_MatrixSpencer_eq_2_14
-- name    : MatrixSpencer.eq_2_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:41:07.713202+00:00
-- url     : https://prove2.me/theorems/772ae848-9651-43ea-8271-bea6e107989c
-- title:
--   Eq. (2.14), p.12 — the potential sum $\sum_k\sqrt{m_k\max\{1,\log(d/m_k)\}}\le\sqrt{nL}/(1-2^{-1/2})^2\le C_0\sqrt n\sqrt{\max\{1,\log(d/n)\}}$
-- statement:
--   This is the summation step of the proof of the main theorem.
--
--   Let $T,n,d\in\mathbb N$, let $m_0,\dots,m_{T-1}$ be integers with $1\le m_k\le 2^{-k}n$, and set $D=\max\{d,n\}$ and $L=1+\log(2D/n)$. Then the series below converge, and
--
--   $$\sum_{k=0}^{T-1}\sqrt{m_k\max\Bigl\{1,\log\frac d{m_k}\Bigr\}}\le\sqrt{nL}\sum_{k=0}^\infty2^{-k/2}\sqrt{1+\frac{k\log2}L}\le\sqrt{nL}\sum_{k=0}^\infty(1+k)2^{-k/2}=\frac{\sqrt{nL}}{(1-2^{-1/2})^2}.$$
--
--   Moreover, the right-hand side is at most $C_0\sqrt n\sqrt{\max\{1,\log(d/n)\}}$, with $C_0=\sqrt{2+\log2}/(1-2^{-1/2})^2$.
--
--   Since the $k$th partial coloring has discrepancy of order $\sqrt{m_k\max\{1,\log(d/m_k)\}}$, this inequality is what sums the rounds of partial coloring into the final bound.
--
--   Differences from the source:
--   - generalization: m_k are the active-set sizes of the run, with T = O(log n) → any T and any integers with 1 ≤ m_k ≤ 2^{−k}n; reason: the page uses only these two properties; the run is a special case
--   - generalization: "for some universal constant C₀ > 0" → the explicit value C₀ = √(2 + log 2)/(1 − 2^{−1/2})²; reason: it is the value of the page's estimate L ≤ (2 + log 2) max{1, log(d/n)}, and it implies the printed existence
--   - encoding: implicit convergence of the two series → Summable is stated in the conclusion; reason: Lean's tsum of a non-summable series is 0
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), proof of Theorem 1.3, (2.14), p.12 (PDF p.14)

import Mathlib

namespace MatrixSpencer

/-- **The potential sum (2.14) and the bound after it, proof of Theorem 1.3.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), proof of Theorem 1.3, (2.14), p.12 (PDF p.14): with `D = max{d, n}` and `L = 1 + log(2D/n)`, and
stages with `1 ≤ m_k ≤ 2^{−k}n`,
`∑_{k<T} √(m_k max{1, log(d/m_k)}) ≤ √(nL) ∑_k 2^{−k/2}√(1 + k log 2 / L) ≤ √(nL) ∑_k (1+k)2^{−k/2} = √(nL)/(1−2^{−1/2})²`,
and the right side is at most `C₀√n√max{1, log(d/n)}`.

**Formalization Note.** The two infinite series are stated summable, so Lean's junk `tsum` is not read.
`C₀` is the value from the page's estimate `L ≤ (2 + log 2) max{1, log(d/n)}`, namely
`√(2 + log 2)/(1 − 2^{−1/2})²`. That is the "some universal constant C₀ > 0" of the page. The sequence
`m` is the page's `m_k`; only the two printed properties of it are assumed. -/
theorem eq_2_14 (T n d : ℕ) (m : ℕ → ℕ) (hm1 : ∀ k < T, 1 ≤ m k)
    (hm2 : ∀ k < T, (m k : ℝ) ≤ (n : ℝ) / 2 ^ k) :
    let L : ℝ := 1 + Real.log (2 * ((max d n : ℕ) : ℝ) / n)
    let a : ℕ → ℝ := fun k => (2 : ℝ) ^ (-(k : ℝ) / 2) * √(1 + (k : ℝ) * Real.log 2 / L)
    let b : ℕ → ℝ := fun k => (1 + (k : ℝ)) * (2 : ℝ) ^ (-(k : ℝ) / 2)
    Summable a ∧ Summable b ∧
    ∑ k ∈ Finset.range T, √((m k : ℝ) * max 1 (Real.log ((d : ℝ) / m k))) ≤
      √((n : ℝ) * L) * ∑' k, a k ∧
    √((n : ℝ) * L) * ∑' k, a k ≤ √((n : ℝ) * L) * ∑' k, b k ∧
    √((n : ℝ) * L) * ∑' k, b k = √((n : ℝ) * L) / (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ 2 ∧
    √((n : ℝ) * L) / (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ 2 ≤
      (√(2 + Real.log 2) / (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ 2) *
        (√(n : ℝ) * √(max 1 (Real.log ((d : ℝ) / n)))) := by sorry

end MatrixSpencer
