-- Prove2me | Theorems.Thm_OnlineUBSR_eq_32_33
-- name    : OnlineUBSR.eq_32_33
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:18:18.749985+00:00
-- url     : https://prove2.me/theorems/75f2c0c5-2222-4dbe-a44f-8fa212377905
-- title:
--   (32)–(33), p.19 — the noise sum is at most $2^s/((s-1)n)$, with (32) and (33) (corrected: third link of (33) not stated)
-- statement:
--   Let $s>1$ be real (in the proof $s=2\mu_1c$) and $n\ge1$. Then
--
--   $$
--   \sum_{k=1}^n\frac1{k^2}\Big(\frac{k+1}{n+1}\Big)^s\le\frac{2^s}{(s-1)\,n}
--   \qquad\text{and}\qquad
--   \sum_{k=1}^n\frac1{k^2}\Big(\frac{n}{k+1}\Big)^{-s}\le\frac{2^{2s}}{(s-1)\,n}.
--   $$
--
--   Moreover (the steps labelled (32) and (33), with $\sigma^2c^2$ factored out)
--
--   $$
--   \sum_{k=1}^n\frac1{k^2}\Big(\frac{n}{k+1}\Big)^{-s}\le\Big(\frac2n\Big)^s\sum_{k=1}^n k^{s-2},
--   \qquad
--   \frac1{n^s}\sum_{k=1}^n k^{s-2}\le\frac{(n+1)^{s-1}}{n^s(s-1)},
--   \qquad
--   \frac1{n^s}\sum_{k=1}^n k^{s-2}\le\frac{2^{s/2}}{(s-1)\,n}.
--   $$
--
--   The first bound, multiplied by $\sigma^2c^2e^{L_1^2c^2\pi^2/6}$, is the noise term of Theorem 1 with the printed constant $2^{2\mu_1c}$; the second is the bound the page reaches at the end of (32), with constant $2^{4\mu_1c}$; the last three are (32), the first two links of (33) and the conclusion of (33).
--
--   **Formalization Note** Powers with exponent $s$ are real powers of positive numbers.
--
--   Differences from the source:
--   - correction: the third link of (33), (n+1)^{2µ₁c−1}/(n^{2µ₁c}(2µ₁c − 1)) ≤ (2^{µ₁c}/(2µ₁c − 1))·(1/n) → not stated; the first two links (clause 4) and the conclusion of (33), (1/n^{2µ₁c})Σ_{k=1}^n k^{2µ₁c−2} ≤ (2^{µ₁c}/(2µ₁c − 1))·(1/n) (clause 5), are stated; reason: that link is false at n = 1 when µ₁c > 1 (µ₁c = 3: 2⁵ = 32 > 8 = 2³), while the conclusion of (33) is true
--   - encoding: ∫₀^{n+1} k^{2µ₁c−2} dk in (33) → its value (n+1)^{s−1}/(s−1); reason: the integral of x^{s−2} with s > 1 over [0, n+1], same value, and no Bochner-integral junk
--   - generalization: the chain (32)–(33), ending in σ²2^{4µ₁c}c²/((2µ₁c − 1)n) → Σ_{k=1}^n (1/k²)((k+1)/(n+1))^s ≤ 2^s/((s − 1)n), and the page's end bound as the second clause; reason: the first clause implies the second, since ((n+1)/n)^s ≤ 2^s, and gives the constant 2^{2µ₁c} of (6)
--   - encoding: exponent 2µ₁c with 1/2 < µ₁c → a real s > 1; reason: s = 2µ₁c
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, Online Estimation and Optimization of Utility-Based Shortfall Risk, arXiv:2111.08805v3, §7.1, eqs. (32)–(33), p.19

import Mathlib

open MeasureTheory ProbabilityTheory Real

namespace OnlineUBSR

/-- **The noise sum, sharpening (32)–(33), p.19.**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, §7.1, (32)–(33), p.19: "≤ exp(L²1c²π²/6) [ z²0/n^{2µ1c} + σ²(2/n)^{2µ1c} Σ_{k=1}^n c²k^{2µ1c−2} ] (32)
[…] (1/n^{2µ1c}) Σ_{k=1}^n k^{2µ1c−2} ≤ (1/n^{2µ1c}) ∫₀^{n+1} k^{2µ1c−2}dk ≤
(n + 1)^{2µ1c−1}/(n^{2µ1c}(2µ1c − 1)) ≤ (2^{µ1c}/(2µ1c − 1)) (1/n). (33)"

For every real `s > 1` (in the proof `s = 2μ₁c`) and every `n ≥ 1`:
1. `Σ_{k=1}^n (1/k²) ((k+1)/(n+1))^s ≤ 2^s / ((s − 1) n)`, the bound that gives the constant of (6);
2. `Σ_{k=1}^n (1/k²) (n/(k+1))^{−s} ≤ 2^{2s} / ((s − 1) n)`, the bound the page reaches at the end of
   (32) (`σ²c²` factored out: `2^{4μ₁c}`), which follows from clause 1;
3. `Σ_{k=1}^n (1/k²) (n/(k+1))^{−s} ≤ (2/n)^s Σ_{k=1}^n k^{s−2}`, the step labelled (32)
   (`σ²c²` factored out; `k + 1 ≤ 2k`);
4. `(1/n^s) Σ_{k=1}^n k^{s−2} ≤ (n+1)^{s−1} / (n^s (s − 1))`, the first two links of (33), with
   `∫₀^{n+1} k^{s−2} dk = (n+1)^{s−1}/(s−1)` evaluated;
5. `(1/n^s) Σ_{k=1}^n k^{s−2} ≤ 2^{s/2} / ((s − 1) n)`, the conclusion of (33) (`2^{μ₁c}`).

**Formalization Note.** Clause 1 is the bound the proof needs to reach the printed constant
`2^{2μ₁c}` of (6). The page's chain (32)–(33) ends with `2^{4μ₁c}` (clause 2), which is weaker
than (6). The third link of (33), `(n+1)^{2μ₁c−1}/(n^{2μ₁c}(2μ₁c − 1)) ≤ 2^{μ₁c}/((2μ₁c − 1) n)`, is
false at `n = 1` when `μ₁c > 1` (at `μ₁c = 3`: `32 > 8`) and is not stated; the conclusion of
(33) itself (clause 5) is true and is stated. Powers are real powers (`Real.rpow`) with positive
bases. -/
theorem eq_32_33
    (s : ℝ) (hs : 1 < s) (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, (1 / (k : ℝ) ^ 2) * (((k : ℝ) + 1) / ((n : ℝ) + 1)) ^ s ≤
      (2 : ℝ) ^ s / ((s - 1) * n) ∧
    ∑ k ∈ Finset.Icc 1 n, (1 / (k : ℝ) ^ 2) * ((n : ℝ) / ((k : ℝ) + 1)) ^ (-s) ≤
      (2 : ℝ) ^ (2 * s) / ((s - 1) * n) ∧
    ∑ k ∈ Finset.Icc 1 n, (1 / (k : ℝ) ^ 2) * ((n : ℝ) / ((k : ℝ) + 1)) ^ (-s) ≤
      (2 / (n : ℝ)) ^ s * ∑ k ∈ Finset.Icc 1 n, (k : ℝ) ^ (s - 2) ∧
    1 / (n : ℝ) ^ s * ∑ k ∈ Finset.Icc 1 n, (k : ℝ) ^ (s - 2) ≤
      ((n : ℝ) + 1) ^ (s - 1) / ((n : ℝ) ^ s * (s - 1)) ∧
    1 / (n : ℝ) ^ s * ∑ k ∈ Finset.Icc 1 n, (k : ℝ) ^ (s - 2) ≤
      (2 : ℝ) ^ (s / 2) / ((s - 1) * n) := by sorry

end OnlineUBSR
