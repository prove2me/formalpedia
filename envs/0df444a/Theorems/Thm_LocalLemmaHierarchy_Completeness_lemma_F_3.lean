-- Prove2me | Theorems.Thm_LocalLemmaHierarchy_Completeness_lemma_F_3
-- name    : LocalLemmaHierarchy.Completeness.lemma_F_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:18:24.613371+00:00
-- url     : https://prove2.me/theorems/42ba6a98-475c-4318-a611-800b1522c0b4
-- title:
--   Lemma F.3 — optimal weights for the Dirichlet-energy bound: $\min E_q=d_q$ at the sine weights
-- statement:
--   Let $q\ge1$ be an integer, $\theta=\pi/(q+1)$ and $d_q=2(1-\cos\theta)$. With $E_q(w)=\sum_{i=0}^q(\sqrt{w_{i+1}}-\sqrt{w_i})^2$ and $w_0=w_{q+1}=0$,
--   $$\min_{w_1,\dots,w_q\ge0,\ \sum_{j=1}^qw_j=1}E_q(w)=d_q.$$
--   The unique minimizing weights are $w_j=\frac2{q+1}\sin^2(j\theta)$, $1\le j\le q$ (F.6). These interior weights are positive and sum to one.
--
--   Differences from the source:
--   - encoding: min … = d_q, with unique minimizer the sine weights → IsLeast of the set of energies of admissible weights at d_q, the sine weights attain d_q, and every admissible w with E_q(w) = d_q equals them on 1, …, q; reason: IsLeast is "attained and a lower bound"; uniqueness is equality of the weights w_1, …, w_q
--   - encoding: weights w_1, …, w_q with w_0 = w_{q+1} = 0 → w : ℕ → ℝ read only on 1, …, q, extended by zero through extWeights; reason: the other values never occur
-- source:
--   Achlioptas, Kritharidis and Zampetakis, A Complete Hierarchy of Local Lemmas, STOC 2027 submission (manuscript sha256 bc1388b0…a434b961), Lemma F.3, printed p. 38 (PDF p. 40); $E_q$ defined printed p. 37 (PDF p. 39); proof printed pp. 38–39 (PDF pp. 40–41)

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Weights

namespace LocalLemmaHierarchy.Completeness

/-- **Lemma F.3 (Optimal weights for the Dirichlet-energy bound)**, printed p. 38 / PDF 40 (proof
printed 38–39). For an integer `q ≥ 1`, `θ = π/(q+1)`, `d_q = 2(1 − cos θ)`: the minimum of
`E_q(w) = ∑_{i=0}^q (√w_{i+1} − √w_i)²` (`w_0 = w_{q+1} = 0`) over `w_1, …, w_q ≥ 0` with
`∑ w_j = 1` is `d_q`; the unique minimizing weights are `w_j = (2/(q+1)) sin²(jθ)` (F.6); these
interior weights are positive and sum to one. -/
theorem lemma_F_3 (q : ℕ) (hq : 1 ≤ q) :
    IsLeast {E : ℝ | ∃ w : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 ≤ w j) ∧
        ∑ j ∈ Finset.Icc 1 q, w j = 1 ∧ dirichletEnergy q w = E} (dq q) ∧
    (∀ w : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 ≤ w j) → ∑ j ∈ Finset.Icc 1 q, w j = 1 →
      dirichletEnergy q w = dq q → ∀ j ∈ Finset.Icc 1 q, w j = sineWeight q j) ∧
    dirichletEnergy q (sineWeight q) = dq q ∧
    (∀ j ∈ Finset.Icc 1 q, 0 < sineWeight q j) ∧
    ∑ j ∈ Finset.Icc 1 q, sineWeight q j = 1 := by sorry

end LocalLemmaHierarchy.Completeness
