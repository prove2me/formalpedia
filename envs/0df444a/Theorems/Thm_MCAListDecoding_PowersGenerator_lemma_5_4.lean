-- Prove2me | Theorems.Thm_MCAListDecoding_PowersGenerator_lemma_5_4
-- name    : MCAListDecoding.PowersGenerator.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:18:06.768181+00:00
-- url     : https://prove2.me/theorems/cc7de00a-0c2d-41e4-913c-a0ceb4ce9d5e
-- title:
--   Lemma 5.4 — adjacent moments μ_{j+1} ≥ (Mv^{j+1} − jv^j)/(M − j)
-- statement:
--   Setting of §5.1 (p. 32): $S$ a finite index set of size $M\ge1$, $A(x)\subseteq[n]$ for $x\in S$, $0\le\gamma<1$, and (5): $\frac1n\sum_{x\in S}|A(x)|\ge M(1-\gamma)$. For $1\le j<M$ set $v=\mu_j^{1/j}$. Then
--   $$\mu_{j+1}\ge\frac{Mv^{j+1}-jv^j}{M-j}.$$
--
--   Differences from the source:
--   - encoding: a finite index set S of size M ≥ 1 → S : Finset ι for an arbitrary type ι, M = S.card; reason: a finite set is a Finset of its ambient type; no instance changes
--   - encoding: (5): (1/n) Σ_i A_i = (1/n) Σ_x |A(x)| ≥ M(1−γ) → M(1−γ) ≤ (1/n) Σ_{x∈S} |A(x)|; reason: the equality in (5) is the double-counting identity, true for every family; only the inequality is a hypothesis
--   - encoding: falling factorials (y)_j with (A_i)_j = 0 when A_i < j → Nat.descFactorial for (A_i)_j and (M)_j; realFalling y j = ∏_{m<j} (y − m) for the real (M(1−γ))_j; reason: Nat.descFactorial is the paper's integer falling factorial including its zero convention
--   - encoding: μ_j^{1/j} → Real.rpow (agreementMoment S A j) (1/j); reason: μ_j ≥ 0, where the real power is the usual j-th root
-- source:
--   Manzur, Mutual Correlated Agreement and List-Decoding: Improvements and Separations, STOC 2027 submission (manuscript of 2026-11-03, sha256 1357b300…), Lemma 5.4, p. 33

import Mathlib
import Definitions.Def_MCAListDecoding_PowersGenerator_Moments

namespace MCAListDecoding.PowersGenerator

/-- Lemma 5.4 (adjacent moments), p. 33. Setting of §5.1 (`|S| = M ≥ 1`, `0 ≤ γ < 1`, (5)).
For `1 ≤ j < M`, with `v = μ_j^{1/j}`, `μ_{j+1} ≥ (M v^{j+1} - j v^j)/(M - j)`. -/
theorem lemma_5_4 {ι : Type*} {n : ℕ} (S : Finset ι) (A : ι → Finset (Fin n)) (γ : ℝ)
    (hM : 1 ≤ S.card) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (h5 : (S.card : ℝ) * (1 - γ) ≤ (1 / (n : ℝ)) * ∑ x ∈ S, ((A x).card : ℝ))
    (j : ℕ) (hj1 : 1 ≤ j) (hjM : j < S.card) :
    ((S.card : ℝ) * (agreementMoment S A j ^ ((1 : ℝ) / (j : ℝ))) ^ (j + 1) -
        (j : ℝ) * (agreementMoment S A j ^ ((1 : ℝ) / (j : ℝ))) ^ j) /
        ((S.card : ℝ) - j) ≤ agreementMoment S A (j + 1) := by sorry

end MCAListDecoding.PowersGenerator
