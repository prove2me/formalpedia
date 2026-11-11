-- Prove2me | Theorems.Thm_MCAListDecoding_PowersGenerator_lemma_5_2
-- name    : MCAListDecoding.PowersGenerator.lemma_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:18:02.326659+00:00
-- url     : https://prove2.me/theorems/ed3da2d2-6319-477c-a1c7-529f4a021d26
-- title:
--   Lemma 5.2 — product bound μ_j ≥ (M(1−γ))_j/(M)_j
-- statement:
--   Setting of §5.1 (p. 32): $S$ a finite index set of size $M\ge1$, $A(x)\subseteq[n]$ for $x\in S$, $0\le\gamma<1$, and (5): $\frac1n\sum_{x\in S}|A(x)|\ge M(1-\gamma)$. If $1\le j\le M$ and $M(1-\gamma)\ge j$, then
--   $$\mu_j\ge\frac{(M(1-\gamma))_j}{(M)_j}.$$
--
--   Differences from the source:
--   - encoding: a finite index set S of size M ≥ 1 → S : Finset ι for an arbitrary type ι, M = S.card; reason: a finite set is a Finset of its ambient type; no instance changes
--   - encoding: (5): (1/n) Σ_i A_i = (1/n) Σ_x |A(x)| ≥ M(1−γ) → M(1−γ) ≤ (1/n) Σ_{x∈S} |A(x)|; reason: the equality in (5) is the double-counting identity, true for every family; only the inequality is a hypothesis
--   - encoding: falling factorials (y)_j with (A_i)_j = 0 when A_i < j → Nat.descFactorial for (A_i)_j and (M)_j; realFalling y j = ∏_{m<j} (y − m) for the real (M(1−γ))_j; reason: Nat.descFactorial is the paper's integer falling factorial including its zero convention
-- source:
--   Manzur, Mutual Correlated Agreement and List-Decoding: Improvements and Separations, STOC 2027 submission (manuscript of 2026-11-03, sha256 1357b300…), Lemma 5.2, p. 32

import Mathlib
import Definitions.Def_MCAListDecoding_PowersGenerator_Moments

namespace MCAListDecoding.PowersGenerator

/-- Lemma 5.2 (product bound), p. 32. Setting of §5.1: a finite index set `S` of size `M ≥ 1`,
sets `A(x) ⊆ [n]`, `0 ≤ γ < 1`, and (5): `(1/n) ∑_{x ∈ S} |A(x)| ≥ M (1 - γ)`. If
`1 ≤ j ≤ M` and `M (1 - γ) ≥ j`, then `μ_j ≥ (M (1 - γ))_j / (M)_j`. -/
theorem lemma_5_2 {ι : Type*} {n : ℕ} (S : Finset ι) (A : ι → Finset (Fin n)) (γ : ℝ)
    (hM : 1 ≤ S.card) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (h5 : (S.card : ℝ) * (1 - γ) ≤ (1 / (n : ℝ)) * ∑ x ∈ S, ((A x).card : ℝ))
    (j : ℕ) (hj1 : 1 ≤ j) (hjM : j ≤ S.card) (hjγ : (j : ℝ) ≤ (S.card : ℝ) * (1 - γ)) :
    realFalling ((S.card : ℝ) * (1 - γ)) j / ((S.card.descFactorial j : ℕ) : ℝ) ≤
      agreementMoment S A j := by sorry

end MCAListDecoding.PowersGenerator
