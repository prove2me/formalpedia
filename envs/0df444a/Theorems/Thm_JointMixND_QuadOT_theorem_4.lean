-- Prove2me | Theorems.Thm_JointMixND_QuadOT_theorem_4
-- name    : JointMixND.QuadOT.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:03.359936+00:00
-- url     : https://prove2.me/theorems/0affcb7f-89b7-4078-9858-d68ceac37622
-- title:
--   Theorem 4, p. 12 — for symmetric 𝓜, each NCD joint mix with marginals F and correlation matrix P*_n minimizes (11)
-- statement:
--   Let $F$ be an $n$-completely mixable distribution on $\mathbb R$ with finite variance, and let $\mathcal M$ be a symmetric set of probabilities on $2^{[n]}$. Then every NCD joint mix $\mathbf X$ with marginals $F$ and correlation matrix $P^*_n$ minimizes (11):
--   $$\sup_{\mu\in\mathcal M}\sum_{K\subseteq[n]}\mathbb E\Big[\Big(\sum_{i\in K}X_i\Big)^2\Big]\mu(K)\;\le\;\sup_{\mu\in\mathcal M}\sum_{K\subseteq[n]}\mathbb E\Big[\Big(\sum_{i\in K}Y_i\Big)^2\Big]\mu(K)$$
--   for every random vector $\mathbf Y$ with $Y_i\sim F$ for all $i\in[n]$.
--
--   This is the existence half of the paper's answer to the multi-marginal problem with quadratic cost under uncertainty about the aggregated subset: negatively dependent joint mixes are optimal for every symmetric uncertainty set.
--
--   **Formalization Note** "Correlation matrix $P^*_n$" is in covariance form, $\operatorname{Cov}(X_i,X_j)=-\operatorname{Var}(F)/(n-1)$ for $i\ne j$, which remains meaningful when $\operatorname{Var}(F)=0$ (allowed by the theorem). The competitor $\mathbf Y$ ranges over all probability laws on $\mathbb R^n$ with all marginals $F$. Components are 0-based in Lean.
-- source:
--   Koike, Lin & Wang, Joint mixability and notions of negative dependence, arXiv:2204.11438v4, p. 12, Theorem 4

import Mathlib
import Definitions.Def_JointMixND_QuadOT_Problems

namespace JointMixND.QuadOT

open MeasureTheory ProbabilityTheory

/-- Theorem 4, p. 12. If `F` is `n`-completely mixable with finite variance and the uncertainty
set `𝓜` is symmetric, then every NCD joint mix with marginals `F` and correlation matrix `P*_n`
minimizes (11) among all random vectors with marginals `F`. -/
theorem theorem_4 {n : ℕ} (F : Measure ℝ) [IsProbabilityMeasure F]
    (hmix : CompletelyMixable n F) (hF2 : MemLp id 2 F)
    (M : Set (Finset (Fin n) → ℝ)) (hM : M ⊆ ProbOnSubsets n) (hsymm : IsSymmetric M)
    (P : Measure (Fin n → ℝ)) (hP : IsCoupling F P) (hJM : IsJointMix P) (hNCD : IsNCD P)
    (hC : HasCorrPstar F P) :
    IsMinimizer11 F M P := by sorry

end JointMixND.QuadOT
