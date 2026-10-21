-- Prove2me | Theorems.Thm_JointMixND_QuadOT_theorem_5
-- name    : JointMixND.QuadOT.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:24.788095+00:00
-- url     : https://prove2.me/theorems/33eab41b-ae1c-4293-bff7-c9c20d772f0f
-- title:
--   Theorem 5, p. 12 — for n ≥ 3, the minimizers of (12), and of (13) for 2 ≤ k ≤ n−2, are exactly the NCD joint mixes with correlation matrix P*_n
-- statement:
--   Let $n\ge 3$ and let $F$ be an $n$-completely mixable distribution on $\mathbb R$ with mean $0$ and finite positive variance. For a random vector $\mathbf X=(X_1,\dots,X_n)$ on a probability space:
--
--   1. $\mathbf X$ is a minimizer to (12),
--   $$\text{minimize}\ \max_{K\subseteq[n]}\mathbb E\Big[\Big(\sum_{i\in K}X_i\Big)^2\Big]\quad\text{subject to }X_i\sim F,\ i\in[n],$$
--   if and only if it is an NCD joint mix with marginals $F$ and correlation matrix $P^*_n$;
--   2. for every $k\in[n]\setminus\{1,n-1,n\}$, $\mathbf X$ is a minimizer to (13),
--   $$\text{minimize}\ \max_{K\subseteq[n],\,|K|=k}\mathbb E\Big[\Big(\sum_{i\in K}X_i\Big)^2\Big]\quad\text{subject to }X_i\sim F,\ i\in[n],$$
--   if and only if it is an NCD joint mix with marginals $F$ and correlation matrix $P^*_n$.
--
--   Assuming a centred marginal, negative dependence is thus not only sufficient but necessary for optimality: every minimizer has the same correlation matrix $P^*_n$. The excluded values of $k$ are those where uniqueness fails (Remark 1).
--
--   **Formalization Note** The random vector is a measurable map `X : Ω → (Fin n → ℝ)` on an arbitrary probability space, and every notion is evaluated on its law; competitors in (12) and (13) range over all probability laws on $\mathbb R^n$ with all marginals $F$. The constraint "$X_i\sim F$" is written explicitly on the right-hand side of each equivalence. $k\in[n]\setminus\{1,n-1,n\}$ is $2\le k\le n-2$ (for $n=3$ this range is empty, as on paper). "Correlation matrix $P^*_n$" is in covariance form. Components are 0-based in Lean.
-- source:
--   Koike, Lin & Wang, Joint mixability and notions of negative dependence, arXiv:2204.11438v4, p. 12, Theorem 5

import Mathlib
import Definitions.Def_JointMixND_QuadOT_Problems

namespace JointMixND.QuadOT

open MeasureTheory ProbabilityTheory

/-- Theorem 5, p. 12. Let `n ≥ 3` and let `F` be `n`-completely mixable with mean `0` and finite
positive variance. A random vector `X` (on any probability space) is a minimizer to (12) if and
only if it is an NCD joint mix with marginals `F` and correlation matrix `P*_n`; the same holds
for (13) with any `k ∈ [n] \ {1, n-1, n}`, i.e. `2 ≤ k ≤ n-2`. -/
theorem theorem_5 (n : ℕ) (hn : 3 ≤ n) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF2 : MemLp id 2 F) (hmean : ∫ t, t ∂F = 0) (hvar : 0 < variance id F)
    (hmix : CompletelyMixable n F)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : Ω → Fin n → ℝ) (hX : AEMeasurable X ℙ) :
    (IsMinimizer12 F (Measure.map X ℙ) ↔
      IsCoupling F (Measure.map X ℙ) ∧ IsJointMix (Measure.map X ℙ) ∧ IsNCD (Measure.map X ℙ) ∧
        HasCorrPstar F (Measure.map X ℙ)) ∧
    ∀ k : ℕ, 2 ≤ k → k ≤ n - 2 →
      (IsMinimizer13 F k (Measure.map X ℙ) ↔
        IsCoupling F (Measure.map X ℙ) ∧ IsJointMix (Measure.map X ℙ) ∧ IsNCD (Measure.map X ℙ) ∧
          HasCorrPstar F (Measure.map X ℙ)) := by sorry

end JointMixND.QuadOT
