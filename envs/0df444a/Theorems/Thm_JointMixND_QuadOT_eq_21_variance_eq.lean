-- Prove2me | Theorems.Thm_JointMixND_QuadOT_eq_21_variance_eq
-- name    : JointMixND.QuadOT.eq_21_variance_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:08.492875+00:00
-- url     : https://prove2.me/theorems/29e88bc4-7668-4283-8754-34ec930ddfac
-- title:
--   Display after (21), p. 28 — a minimizer of (13) has Var(Σ_{i∈K} X_i) = σ²k(n−k)/(n−1) for each |K| = k
-- statement:
--   Let $n\ge 2$, $1\le k\le n$, and let $F$ be $n$-completely mixable with mean $0$ and finite variance $\sigma^2=\operatorname{Var}(F)$. If $\mathbf X$ is a minimizer to (13), i.e. $\mathbf X$ has marginals $F$ and minimizes $\max_{K\subseteq[n],|K|=k}\mathbb E[(\sum_{i\in K}X_i)^2]$ among all random vectors with marginals $F$, then
--   $$\operatorname{Var}\Big(\sum_{i\in K}X_i\Big)=\sigma^2\,\frac{k(n-k)}{n-1}\qquad\text{for each }K\subseteq[n]\text{ with }|K|=k.$$
--
--   This is the step of the proof of Theorem 5 that pins down the variance of every $k$-subset sum of a minimizer, from which its correlation matrix is recovered.
--
--   **Formalization Note** The paper normalizes $\operatorname{Var}(F)=1$; the factor $\sigma^2$ is kept. Complete mixability supplies the comparison vector $\mathbf X^{\mathrm E}$ in (21). The hypothesis $n\ge 3$ and the exclusion of $k\in\{1,n-1,n\}$ from Theorem 5 are not needed for this step and are not imposed.
-- source:
--   Koike, Lin & Wang, Joint mixability and notions of negative dependence, arXiv:2204.11438v4, p. 28, display after (21) in the Proof of Theorem 5

import Mathlib
import Definitions.Def_JointMixND_QuadOT_Problems

namespace JointMixND.QuadOT

open MeasureTheory ProbabilityTheory

/-- Display after (21), p. 28. Let `F` be `n`-completely mixable with mean `0` and finite variance
`σ² = Var(F)`, `n ≥ 2`, `1 ≤ k ≤ n`. If `X` is a minimizer to (13) for `k`, then
`Var(∑_{i∈K} X_i) = σ² k(n-k)/(n-1)` for each `K` with `|K| = k`. -/
theorem eq_21_variance_eq {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF2 : MemLp id 2 F) (hmean : ∫ t, t ∂F = 0)
    (hmix : CompletelyMixable n F)
    (P : Measure (Fin n → ℝ)) (hmin : IsMinimizer13 F k P) :
    ∀ K : Finset (Fin n), K.card = k →
      variance (fun x => ∑ i ∈ K, x i) P =
        variance id F * ((k : ℝ) * ((n : ℝ) - (k : ℝ))) / ((n : ℝ) - 1) := by sorry

end JointMixND.QuadOT
