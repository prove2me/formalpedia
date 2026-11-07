-- Prove2me | Theorems.Thm_LineVsPoint_lemma_2_1
-- name    : LineVsPoint.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:04:45.166053+00:00
-- url     : https://prove2.me/theorems/38d4f3b4-2394-42ab-8306-1a8189c25d2e
-- title:
--   Lemma 2.1 — expander mixing for points and affine $k$-flats
-- statement:
--   **Lemma 2.1** (cited from Lund–Saraf, [LS16, Theorem 1]). Let $\mathbb F_q$ be a finite field, $1\le k<m$, $X\subseteq\mathbb F_q^m$, and let $\mathcal T$ be a family of affine $k$-dimensional subspaces. Then
--
--   $$
--   \Bigl|\Pr_{W,\,x\in W}[x\in X,\ W\in\mathcal T]-\mu(X)\mu(\mathcal T)\Bigr|\le\lambda_{m,k}\sqrt{\mu(X)\mu(\mathcal T)},\qquad
--   \lambda_{m,k}^2=\frac{q^{m-k}-1}{q^m-1}.
--   $$
--
--   In particular,
--
--   1. $\lambda_{2,1}=1/\sqrt{q+1}$;
--   2. $\lambda_{m,1}\le q^{-1/2}$ for every $m\ge 2$;
--   3. $\lambda_{m,2}\le q^{-1}$ for every $m\ge 3$.
--
--   Here $W$ is a uniformly random $k$-flat and $x$ a uniformly random point of $W$, $\mu(X)=|X|/q^m$ and $\mu(\mathcal T)$ is the fraction of all $k$-flats in $\mathcal T$. The lemma is the incidence-graph expansion used in Lemma 3.4, Lemma 4.1 (ii) and the list-decoding step of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: λ_{m,k} given by λ²_{m,k} = (q^{m−k} − 1)/(q^m − 1) → the nonnegative square root lamMix q m k; reason: λ_{m,k} ≥ 0 is the mixing parameter whose square the page displays
--   - encoding: the 'in particular' clauses, under the lemma's hypothesis 1 ≤ k < m → λ_{m,1} ≤ q^{−1/2} for m ≥ 2 and λ_{m,2} ≤ q^{−1} for m ≥ 3; reason: these are the ranges 1 ≤ k < m in which the lemma defines λ_{m,k}
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), Lemma 2.1, p.10

import Definitions.Def_LineVsPoint_flatIncProb

set_option autoImplicit false

universe u

namespace LineVsPoint

/-- **Lemma 2.1** (expander mixing for points and affine subspaces, cited from [LS16, Theorem 1]).
*Let `1 ≤ k < m`, let `X ⊆ F^m_q`, and let `T` be a family of affine `k`-dimensional subspaces.
Then `|Pr_{W, x ∈ W}[x ∈ X, W ∈ T] − µ(X)µ(T)| ≤ λ_{m,k} √(µ(X)µ(T))`,
`λ²_{m,k} = (q^{m−k} − 1)/(q^m − 1)`. In particular, `λ_{2,1} = 1/√(q + 1)`,
`λ_{m,1} ≤ q^{−1/2}`, and `λ_{m,2} ≤ q^{−1}`.*
Dao, Kominers, Thaler, Zheng, *Cube-Root Soundness Is Optimal for the Line–versus–Point Test*
(manuscript, sha256 328a8943…), Lemma 2.1, p.10.

**Formalization Note.** `λ_{m,k}` is the nonnegative square root `lamMix q m k`. The three "in
particular" clauses are stated in the ranges where Lemma 2.1 defines `λ_{m,k}` (`1 ≤ k < m`):
`m ≥ 2` for `k = 1` and `m ≥ 3` for `k = 2`. -/
theorem lemma_2_1 :
    ∀ (F : Type u) [Field F] [Fintype F],
      (∀ (m k : ℕ), 1 ≤ k → k < m →
        ∀ (X : Finset (Fin m → F)) (T : Finset (AffFlat F m k)),
          |flatIncProb X T - ptMeasure X * flatMeasure T| ≤
            lamMix (Fintype.card F) m k * Real.sqrt (ptMeasure X * flatMeasure T)) ∧
      lamMix (Fintype.card F) 2 1 = 1 / Real.sqrt ((Fintype.card F : ℝ) + 1) ∧
      (∀ m : ℕ, 2 ≤ m → lamMix (Fintype.card F) m 1 ≤ (Fintype.card F : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      (∀ m : ℕ, 3 ≤ m → lamMix (Fintype.card F) m 2 ≤ (Fintype.card F : ℝ)⁻¹) := by sorry

end LineVsPoint
