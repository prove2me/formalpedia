-- Prove2me | Theorems.Thm_HMajConsensus_corollary_5_18_sample_size_majorization
-- name    : HMajConsensus.corollary_5_18_sample_size_majorization
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:13:35.780217+00:00
-- url     : https://prove2.me/theorems/c1d94c26-9dfa-4b8c-be2a-d738dd1e3367
-- title:
--   Corollary 5.18 — $q^{(h)}(p)\succeq q^{(r)}(p)\succeq p$ for $h\ge r\ge2$, and $q^{(2)}(p)=p$
-- statement:
--   For a probability vector $p$ on $[k]$ and a sample size $r$, let $q^{(r)}(p)=(q^{(r)}_i(p))_{i\in[k]}$ be the winner distribution, $q^{(r)}_i(p)=\Pr[\mathrm{Maj}(X)=i]$ with $X\sim\mathrm{Multinomial}(r;p)$ and uniform tie-breaking. For nonnegative vectors $x,y\in\mathbb R^k$ with equal sums, $x\succeq y$ (majorization) means $\sum_{i=1}^bx^\downarrow_i\ge\sum_{i=1}^by^\downarrow_i$ for every $b\in[k]$, where $x^\downarrow,y^\downarrow$ are the nonincreasing rearrangements. Then for all integers $h\ge r\ge2$,
--   $$q^{(h)}(p)\ \succeq\ q^{(r)}(p)\ \succeq\ p,\qquad\text{and}\qquad q^{(2)}(p)=p.$$
--
--   Larger samples make the next-round distribution more concentrated; this is the comparison behind the coupling of $h$-Majority with Voter (Theorem 5.14).
--
--   **Formalization Note** $x\succeq y$ is the published `AgriSubsidy.Combined.Majorizes x y`: the largest sum of $b$ coordinates of $x$ dominates that of $y$ for every $b\le k$, and the totals agree; for nonnegative vectors the largest sum of $b$ coordinates is the $b$-th prefix sum of the nonincreasing rearrangement, so this is Definition 5.13.
--
--   Differences from the source:
--   - encoding: x ⪰ y via prefix sums of nonincreasing rearrangements (Definition 5.13) → AgriSubsidy.Combined.Majorizes x y (largest b-coordinate sums, b ≤ k, and equal totals); reason: the largest sum of b coordinates is the b-th prefix sum of x↓; same relation on the vectors of the statement
--   - encoding: nodes [n], opinions [k]; log n and ln n → Fin n, Fin k (0-based labels); Real.log; reason: Lean convention; the paper's log is natural (Lemma 6.9 and 7.2 proofs turn exp(−A log n) into n^{−A}); same instances
-- source:
--   d'Amore, Rybicki, Shimizu, Shiraga, Vacus, Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics, arXiv:2610.40562, Corollary 5.18, p.27 (with Definition 5.13, p.25, and Lemma 5.15, p.25: every probability vector p)

import Mathlib
import Definitions.Def_HMajConsensus_majLaw
import Definitions.Def_AgriSubsidy_Combined_Majorization

open MeasureTheory ProbabilityTheory

namespace HMajConsensus

/-- **Corollary 5.18** (d'Amore, Rybicki, Shimizu, Shiraga, Vacus, *Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics*, arXiv:2610.40562, §5.2, p.27): for integers `h ≥ r ≥ 2`,
`q^{(h)}(p) ⪰ q^{(r)}(p) ⪰ p`; moreover `q^{(2)}(p) = p`.

**Formalization Note** For every probability vector `p` (Lemma 5.15, p.25). `x ⪰ y` is the
published `AgriSubsidy.Combined.Majorizes x y` (top-`b` sums of `x` dominate those of `y` and the
totals agree), which is Definition 5.13 for nonnegative vectors. -/
theorem corollary_5_18_sample_size_majorization {k : ℕ} (p : PMF (Fin k)) (h r : ℕ)
    (hr : 2 ≤ r) (hrh : r ≤ h) :
    AgriSubsidy.Combined.Majorizes (winVec h p) (winVec r p) ∧
      AgriSubsidy.Combined.Majorizes (winVec r p) (probVec p) ∧
      winVec 2 p = probVec p := by sorry

end HMajConsensus
