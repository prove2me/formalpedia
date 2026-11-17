-- Prove2me | Theorems.Thm_IntervalToDynamic_Supplement_theorem_3
-- name    : IntervalToDynamic.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:39:46.393619+00:00
-- url     : https://prove2.me/theorems/bd6de677-b912-4807-bea9-f5731f4c7184
-- title:
--   Theorem 3 — geometric characterization of the metric-level implication
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^d$ be nonempty, compact and convex. Let $\tau(T)\ge1$ eventually with $\tau(T)/T\to0$, and let $A_T\ge1$ eventually. The following are equivalent:
--
--   1. There is a constant $C>0$ such that, for all sufficiently large $T$, every norm-$1$ bounded linear loss sequence, every $\mathcal X$-valued decision sequence satisfying all OIR bounds $A_T\sqrt{|I|}$, and every $\mathcal X$-valued comparator path with $P_T\le\tau(T)$ satisfy
--      $$\operatorname{D-Reg}_T\le C A_T\sqrt{\tau(T)T}.$$
--   2. There are fixed $r_0,C'>0$ such that, for all sufficiently large $T$,
--      $$\Gamma_{\mathcal X}(r_0)\le C'A_T\sqrt{\tau(T)/T}.$$
--
--   Both constants precede the varying horizon and adversarial sequences, exactly expressing the theorem's independence clause.
--
--   Differences from the source:
--   - encoding: asymptotic $O$ bounds in $T$ with $A_T$ and $\tau$ varying → explicit positive constants before eventual horizon quantifiers and, on the regret side, before every loss, decision and comparator sequence; reason: this records the printed uniformity of all implicit constants
--   - encoding: the OCO setup implicitly uses a genuine Euclidean dimension and feasible domain → explicit hypotheses $d>0$ and $\mathcal X\ne\varnothing$; reason: these only exclude the empty/undefined geometric cases and are standing conventions of the paper's online-learning model
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Theorem 3, p.6 (PDF p.8); proof, pp.16–23 (PDF pp.18–25)

import Mathlib
import Definitions.Def_IntervalToDynamic_Supplement_Geometry

open Filter
open ModernOnlineLearning.Dynamic (dynamicRegret pathLength)

namespace IntervalToDynamic.Supplement

/-- Theorem 3 (geometric characterization of the metric-level implication), Wang--Zhao--Zhou,
*On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, p.6
(PDF p.8).

The `O` constants are existentially quantified before the horizon and before every loss, decision,
and comparator sequence. Thus they may depend on the fixed geometry (and on `r₀` on the right),
but not on the varying adversarial data. -/
theorem theorem_3 {d : ℕ} (hd : 0 < d) (X : Set (EuclideanSpace ℝ (Fin d)))
    (hXc : IsCompact X) (hXv : Convex ℝ X) (hXn : X.Nonempty)
    (tau A : ℕ → ℝ) (htau1 : ∀ᶠ T in atTop, 1 ≤ tau T)
    (htauo : Tendsto (fun T : ℕ => tau T / T) atTop (nhds 0))
    (hA : ∀ᶠ T in atTop, 1 ≤ A T) :
    (∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℕ in atTop,
      ∀ (g : ℕ → EuclideanSpace ℝ (Fin d))
        (x u : ℕ → EuclideanSpace ℝ (Fin d)),
        (∀ t ∈ Finset.Icc 1 T, ‖g t‖ ≤ 1) →
        (∀ t ∈ Finset.Icc 1 T, x t ∈ X ∧ u t ∈ X) →
        SatisfiesOIR (T := T) X (fun t z => inner ℝ (g t) z) x (A T)
          (fun n => Real.sqrt n) →
        pathLength u T ≤ tau T →
        dynamicRegret (fun t z => inner ℝ (g t) z) x u T ≤
          C * A T * Real.sqrt (tau T * T)) ↔
    (∃ r0 C : ℝ, 0 < r0 ∧ 0 < C ∧ ∀ᶠ T : ℕ in atTop,
      capProfile X r0 ≤ C * A T * Real.sqrt (tau T / T)) := by sorry

end IntervalToDynamic.Supplement
