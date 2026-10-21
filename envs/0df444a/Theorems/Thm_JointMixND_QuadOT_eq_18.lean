-- Prove2me | Theorems.Thm_JointMixND_QuadOT_eq_18
-- name    : JointMixND.QuadOT.eq_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:58.856837+00:00
-- url     : https://prove2.me/theorems/d145b376-bb82-4b7b-a08e-5b1a1e005a8b
-- title:
--   (18), p. 28 — under correlation matrix P*_n and mean 0, E[(Σ_{i∈K} X_i)²] = σ²|K|(n−|K|)/(n−1); the max over K is σ²k*(n−k*)/(n−1)
-- statement:
--   Let $n\ge 2$ and let $F$ have mean $0$ and finite variance $\sigma^2=\operatorname{Var}(F)$. Let $\mathbf X^{\mathrm E}$ have marginals $F$ and correlation matrix $P^*_n$. Then for every $K\subseteq[n]$,
--   $$\mathbb E\Big[\Big(\sum_{i\in K}X^{\mathrm E}_i\Big)^2\Big]=\operatorname{Var}\Big(\sum_{i\in K}X^{\mathrm E}_i\Big)=\sigma^2\,\frac{|K|\,(n-|K|)}{n-1},$$
--   and consequently the objective of (12) at $\mathbf X^{\mathrm E}$ is
--   $$\max_{K\subseteq[n]}\mathbb E\Big[\Big(\sum_{i\in K}X^{\mathrm E}_i\Big)^2\Big]=\sigma^2\max_{k\in[n]}\frac{k(n-k)}{n-1}=\sigma^2\,\frac{k^*(n-k^*)}{n-1},\qquad k^*=\lfloor n/2\rfloor .$$
--
--   By Theorem 4 this is the optimal value of (12); the proof of Theorem 5 compares minimizers against it.
--
--   **Formalization Note** The paper normalizes $\operatorname{Var}(F)=1$ "without loss of generality"; here the variance factor $\sigma^2$ is kept. The vector is only assumed to have marginals $F$ and covariance $-\sigma^2/(n-1)$ off the diagonal (this already makes it an NCD joint mix). All arithmetic is in $\mathbb R$ with casts before subtraction; $k^*$ is natural-number division `n / 2`. The empty set contributes the value $0$.
-- source:
--   Koike, Lin & Wang, Joint mixability and notions of negative dependence, arXiv:2204.11438v4, p. 28, (18)

import Mathlib
import Definitions.Def_JointMixND_QuadOT_Problems

namespace JointMixND.QuadOT

open MeasureTheory ProbabilityTheory

/-- (18), p. 28. Let `F` have mean `0` and finite variance `σ² = Var(F)`, and let `X^E` have
marginals `F` and correlation matrix `P*_n` (`n ≥ 2`). Then
`E[(∑_{i∈K} X^E_i)^2] = σ² |K|(n-|K|)/(n-1)` for every `K ⊆ [n]`, and the objective of (12) at
`X^E` is `max_{K⊆[n]} E[(∑_{i∈K} X^E_i)^2] = σ² k*(n-k*)/(n-1)` with `k* = ⌊n/2⌋`. -/
theorem eq_18 {n : ℕ} (hn : 2 ≤ n) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF2 : MemLp id 2 F) (hmean : ∫ t, t ∂F = 0)
    (P : Measure (Fin n → ℝ)) (hP : IsCoupling F P) (hC : HasCorrPstar F P) :
    (∀ K : Finset (Fin n), ∫ x, (∑ i ∈ K, x i) ^ 2 ∂P =
        variance id F * ((K.card : ℝ) * ((n : ℝ) - (K.card : ℝ))) / ((n : ℝ) - 1)) ∧
    maxCost P =
      variance id F * (((n / 2 : ℕ) : ℝ) * ((n : ℝ) - ((n / 2 : ℕ) : ℝ))) / ((n : ℝ) - 1) := by sorry

end JointMixND.QuadOT
