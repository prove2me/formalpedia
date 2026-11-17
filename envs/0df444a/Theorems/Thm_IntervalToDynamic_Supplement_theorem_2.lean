-- Prove2me | Theorems.Thm_IntervalToDynamic_Supplement_theorem_2
-- name    : IntervalToDynamic.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:39:14.741668+00:00
-- url     : https://prove2.me/theorems/400de6a9-39f7-430a-97fc-d8ebfc2b7d1d
-- title:
--   Theorem 2 — homogeneous aggregation represents all proofs
-- statement:
--   Fix a positive horizon, a nonempty compact convex domain $\mathcal X$, continuous losses $f_t:\mathcal X\to\mathbb R$, a comparator path in $\mathcal X$, a nonnegative nondecreasing rate $\rho$, and $A_T\ge1$. Among all actual $\mathcal X$-valued decision sequences satisfying every OIR constraint
--   $$
--   \operatorname{I-Reg}_I(z)\le A_T\rho(|I|)
--   $$
--   simultaneously for all intervals and all $z\in\mathcal X$, dynamic regret has a maximizing sequence $x^*$. Among all homogeneous fractional interval covers, the singleton-corrected dual objective has a minimizing cover $\lambda^*$. These attained values are equal:
--   $$
--   \operatorname{D-Reg}_T(x^*,u)=\sum_I\lambda_I^*c_I-\sum_{t=1}^Tf_t(u_t).
--   $$
--   Here $c_I$ is exactly the paper's cost, including $c_{\{t\}}=\min\{m_t+A_T\rho(1),M_t\}$.
--
--   This equality characterizes the strongest dynamic-regret conclusion obtainable from the OIR inequalities alone.
--
--   Differences from the source:
--   - encoding: attained maximum and minimum notation → explicit maximizing decision sequence and minimizing homogeneous cover, with universal optimality clauses and equality of their values; reason: real suprema and infima are total in Lean and have junk defaults, whereas witnesses express both attainment claims literally
--   - generalization: $\mathcal X\subseteq\mathbb R^d$ → a nonempty compact convex subset of an arbitrary real normed vector space; reason: the LP argument uses only compactness, convexity and continuity, and the Lean statement specializes to the paper by taking Euclidean space
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Theorem 2, p.5 (PDF p.7); proof, pp.15–16 (PDF pp.17–18)

import Mathlib
import Definitions.Def_IntervalToDynamic_Supplement_Geometry

open ModernOnlineLearning.Dynamic (dynamicRegret)

namespace IntervalToDynamic.Supplement

/-- Theorem 2 (homogeneous aggregation represents all proofs), Wang--Zhao--Zhou,
*On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, p.5
(PDF p.7).

The two extrema are expressed by maximizing/minimizing witnesses, avoiding any default value of a
real `sSup` or `sInf`. The primal ranges over actual `X`-valued decision sequences satisfying every
Eq. (4) constraint; the dual ranges over homogeneous fractional covers, not partitions. -/
theorem theorem_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℕ) (hT : 1 ≤ T) (X : Set E) (hXc : IsCompact X) (hXv : Convex ℝ X)
    (hXn : X.Nonempty) (f : ℕ → E → ℝ)
    (hf : ∀ t ∈ Finset.Icc 1 T, ContinuousOn (f t) X)
    (u : ℕ → E) (hu : ∀ t ∈ Finset.Icc 1 T, u t ∈ X)
    (rho : ℕ → ℝ) (hrho : ∀ n, 0 ≤ rho n)
    (hrho_mono : Monotone rho) (A : ℝ) (hA : 1 ≤ A) :
    ∃ (xStar : ℕ → E) (lamStar : RoundInterval T → ℝ),
      (∀ t ∈ Finset.Icc 1 T, xStar t ∈ X) ∧
      SatisfiesOIR (T := T) X f xStar A rho ∧ IsHomogeneous lamStar ∧
      (∀ x : ℕ → E, (∀ t ∈ Finset.Icc 1 T, x t ∈ X) →
        SatisfiesOIR (T := T) X f x A rho →
        dynamicRegret f x u T ≤ dynamicRegret f xStar u T) ∧
      (∀ lam : RoundInterval T → ℝ, IsHomogeneous lam →
        aggregationValue X f u A rho lamStar ≤ aggregationValue X f u A rho lam) ∧
      dynamicRegret f xStar u T = aggregationValue X f u A rho lamStar := by sorry

end IntervalToDynamic.Supplement
