-- Prove2me | Theorems.Thm_MCAListDecoding_PowersGenerator_corollary_5_3
-- name    : MCAListDecoding.PowersGenerator.corollary_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:18:12.156688+00:00
-- url     : https://prove2.me/theorems/2c466050-fe9f-41b3-b702-0395476970d2
-- title:
--   Corollary 5.3 — μ_j^{1/j} ≥ 1 − γ − (j−1)γ/(M−j+1)
-- statement:
--   Setting of §5.1 (p. 32): $S$ a finite index set of size $M\ge1$, $A(x)\subseteq[n]$ for $x\in S$, $0\le\gamma<1$, and (5): $\frac1n\sum_{x\in S}|A(x)|\ge M(1-\gamma)$. Assume $j\ge1$, $M\ge2j$ and $1-\gamma>1/2$. Then
--   $$\mu_j^{1/j}\ge 1-\gamma-\frac{(j-1)\gamma}{M-j+1}.$$
--
--   Differences from the source:
--   - encoding: a finite index set S of size M ≥ 1 → S : Finset ι for an arbitrary type ι, M = S.card; reason: a finite set is a Finset of its ambient type; no instance changes
--   - encoding: (5): (1/n) Σ_i A_i = (1/n) Σ_x |A(x)| ≥ M(1−γ) → M(1−γ) ≤ (1/n) Σ_{x∈S} |A(x)|; reason: the equality in (5) is the double-counting identity, true for every family; only the inequality is a hypothesis
--   - encoding: falling factorials (y)_j with (A_i)_j = 0 when A_i < j → Nat.descFactorial for (A_i)_j and (M)_j; realFalling y j = ∏_{m<j} (y − m) for the real (M(1−γ))_j; reason: Nat.descFactorial is the paper's integer falling factorial including its zero convention
--   - encoding: μ_j^{1/j} → Real.rpow (agreementMoment S A j) (1/j); reason: μ_j ≥ 0, where the real power is the usual j-th root
-- source:
--   Manzur, Mutual Correlated Agreement and List-Decoding: Improvements and Separations, STOC 2027 submission (manuscript of 2026-11-03, sha256 1357b300…), Corollary 5.3, p. 33

import Mathlib
import Definitions.Def_MCAListDecoding_PowersGenerator_Moments

namespace MCAListDecoding.PowersGenerator

/-- Corollary 5.3 (a lower bound on the moment root), p. 33. Setting of §5.1 (`|S| = M ≥ 1`,
`0 ≤ γ < 1`, (5)). If `j ≥ 1`, `M ≥ 2 j` and `1 - γ > 1/2`, then
`μ_j^{1/j} ≥ 1 - γ - (j - 1) γ / (M - j + 1)`. -/
theorem corollary_5_3 {ι : Type*} {n : ℕ} (S : Finset ι) (A : ι → Finset (Fin n)) (γ : ℝ)
    (hM : 1 ≤ S.card) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (h5 : (S.card : ℝ) * (1 - γ) ≤ (1 / (n : ℝ)) * ∑ x ∈ S, ((A x).card : ℝ))
    (j : ℕ) (hj1 : 1 ≤ j) (hjM : 2 * j ≤ S.card) (hhalf : 1 / 2 < 1 - γ) :
    1 - γ - ((j : ℝ) - 1) * γ / ((S.card : ℝ) - j + 1) ≤
      agreementMoment S A j ^ ((1 : ℝ) / (j : ℝ)) := by sorry

end MCAListDecoding.PowersGenerator
