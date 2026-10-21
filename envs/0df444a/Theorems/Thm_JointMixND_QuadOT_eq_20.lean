-- Prove2me | Theorems.Thm_JointMixND_QuadOT_eq_20
-- name    : JointMixND.QuadOT.eq_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:56.750872+00:00
-- url     : https://prove2.me/theorems/31b2fb51-ad03-46e8-bbc6-4ecd289a8d6e
-- title:
--   (20), p. 28 — for identical marginals, the average of Var(Σ_{i∈K} X_i) over |K| = k is at least σ²k(n−k)/(n−1)
-- statement:
--   Let $n\ge 2$, $1\le k\le n$, and let $F$ have finite variance $\sigma^2=\operatorname{Var}(F)$. Let $K_\ell$, $\ell=1,\dots,n_k$, be all subsets of $[n]$ with cardinality $k$, where $n_k=\binom nk$. For every random vector $\mathbf X$ with identical marginals $F$,
--   $$\frac1{n_k}\sum_{\ell=1}^{n_k}\operatorname{Var}\Big(\sum_{i\in K_\ell}X_i\Big)\;\ge\;\sigma^2\Big(k-\frac{k(k-1)}{n-1}\Big)=\sigma^2\,\frac{k(n-k)}{n-1}.$$
--
--   Combined with (18), it shows that a minimizer of (13) must have every $k$-subset variance equal to the common value attained under $P^*_n$.
--
--   **Formalization Note** The paper normalizes $\operatorname{Var}(F)=1$; the factor $\sigma^2$ is kept here. Arithmetic is in $\mathbb R$, with the sum taken over `Finset.powersetCard k univ`.
-- source:
--   Koike, Lin & Wang, Joint mixability and notions of negative dependence, arXiv:2204.11438v4, p. 28, (20)

import Mathlib
import Definitions.Def_JointMixND_QuadOT_Problems

namespace JointMixND.QuadOT

open MeasureTheory ProbabilityTheory

/-- (20), p. 28. For any random vector `X` with identical marginals `F` of finite variance
`σ² = Var(F)`, `n ≥ 2` and `1 ≤ k ≤ n`, the average of `Var(∑_{i∈K} X_i)` over the `binom(n,k)`
subsets `K` of cardinality `k` is at least `σ² k(n-k)/(n-1)`. -/
theorem eq_20 {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF2 : MemLp id 2 F)
    (P : Measure (Fin n → ℝ)) (hP : IsCoupling F P) :
    variance id F * ((k : ℝ) * ((n : ℝ) - (k : ℝ))) / ((n : ℝ) - 1) ≤
      (∑ K ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
          variance (fun x => ∑ i ∈ K, x i) P) / (n.choose k : ℝ) := by sorry

end JointMixND.QuadOT
