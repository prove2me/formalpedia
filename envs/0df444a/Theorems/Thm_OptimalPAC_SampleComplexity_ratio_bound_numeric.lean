-- Prove2me | Theorems.Thm_OptimalPAC_SampleComplexity_ratio_bound_numeric
-- name    : OptimalPAC.SampleComplexity.ratio_bound_numeric
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:28:47.785744+00:00
-- url     : https://prove2.me/theorems/70b97ce2-51c0-4546-aa8e-bec84a326c8a
-- title:
--   Numerical core of the induction step: bound (8) and its comparison with $\frac{150}{m+1}\left(d+\ln\frac{18}\delta\right)$
-- statement:
--   Let $c=1800$, let $m$ and $d\ge1$ be integers with $m>c\ln(18e)-1$, let $\delta\in(0,1)$, and write $q=\lfloor m/4\rfloor$.
--
--   1. For every real $p$ and integer $N$ with
--   $$\frac{23}{q}\ln\left(\frac9\delta\right)\le p\le\frac{4c}m\left(d+\ln\left(\frac{9\cdot18}\delta\right)\right)\quad\text{and}\quad N\ge\frac7{10}\,p\,q,$$
--   one has
--   $$p\cdot\frac2N\left(d\,\mathrm{Log}_2\left(\frac{2eN}d\right)+\mathrm{Log}_2\left(\frac{18}\delta\right)\right)<\frac{150}{m+1}\left(d+\ln\left(\frac{18}\delta\right)\right).$$
--   2. $$\frac{23}{q}\ln\left(\frac9\delta\right)<\frac{150}{m+1}\left(d+\ln\left(\frac{18}\delta\right)\right).$$
--
--   In the proof of Theorem 2, $p=\mathcal P(\mathrm{ER}(h_i))$, the upper bound on $p$ is the inductive bound (6), the lower bound on $N=N_i$ is the event $E_i''$, and the left side of part 1 is the right side of (7). Part 1 is the chain of inequalities ending in (8) together with the numerical comparison that follows it; part 2 is the comparison used when $p$ is below the threshold. Together they give $\mathcal P(\mathrm{ER}(h_i)\cap\mathrm{ER}(h))<\frac{150}{m+1}(d+\ln(18/\delta))$.
--
--   **Formalization Note** $\lfloor m/4\rfloor$ is natural-number division, cast to the reals. The statement is deterministic: it isolates the arithmetic of pp. 9–10 from the probabilistic events. The constant $150$ is tight (the paper's relaxation gives $149.9997$), so no constant is rounded.
-- source:
--   Hanneke, The Optimal Sample Complexity of PAC Learning, arXiv:1507.00473v4, proof of Theorem 2, pp. 9–10 (eqs. (6), (7), the chain ending in (8), and the two comparisons with 150/(m+1)(d + ln(18/δ)))

import Mathlib
import Definitions.Def_OptimalPAC_SampleComplexity_Model

namespace OptimalPAC.SampleComplexity

/-- The numerical part of the proof of Theorem 2 (Hanneke 2016, pp. 9–10: the chain ending in (8)
and the two comparisons with `(150/(m+1))(d + ln(18/δ))` after it), with `c = 1800`. Let
`m > c ln(18e) − 1`, `d ≥ 1`, `δ ∈ (0,1)`, and write `q = ⌊m/4⌋`.
(a) If `p ≥ (23/q) ln(9/δ)`, `p ≤ (4c/m)(d + ln(9·18/δ))` (eq. (6)) and `N ≥ (7/10) p q` (the
event `E_i''`), then the right-hand side of (7),
`p (2/N)(d Log₂(2eN/d) + Log₂(18/δ))`, is less than `(150/(m+1))(d + ln(18/δ))`.
(b) `(23/q) ln(9/δ) < (150/(m+1))(d + ln(18/δ))`. -/
theorem ratio_bound_numeric (m d : ℕ) (hm : 1800 * Real.log (18 * Real.exp 1) - 1 < m)
    (hd : 1 ≤ d) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∀ (p : ℝ) (N : ℕ),
      23 / ((m / 4 : ℕ) : ℝ) * Real.log (9 / δ) ≤ p →
      p ≤ 4 * 1800 / (m : ℝ) * (d + Real.log (9 * 18 / δ)) →
      7 / 10 * p * ((m / 4 : ℕ) : ℝ) ≤ N →
      p * (2 / (N : ℝ) * ((d : ℝ) * Log2 (2 * Real.exp 1 * N / d) + Log2 (18 / δ))) <
        150 / ((m : ℝ) + 1) * (d + Real.log (18 / δ))) ∧
    23 / ((m / 4 : ℕ) : ℝ) * Real.log (9 / δ) <
      150 / ((m : ℝ) + 1) * (d + Real.log (18 / δ)) := by sorry

end OptimalPAC.SampleComplexity
