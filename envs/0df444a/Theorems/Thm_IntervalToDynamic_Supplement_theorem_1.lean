-- Prove2me | Theorems.Thm_IntervalToDynamic_Supplement_theorem_1
-- name    : IntervalToDynamic.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:38:50.377838+00:00
-- url     : https://prove2.me/theorems/786b9469-ede2-43db-a14e-7487cd81d89e
-- title:
--   Theorem 1 — OIR does not imply ODR on general convex domains
-- statement:
--   There are absolute constants $c_{\rm lin},c_{\rm quad}>0$ such that, for every path-length budget family $\tau(T)$ with $\tau(T)\ge1$ eventually and $\tau(T)/T\to0$, the following hold for every sufficiently large $T$:
--
--   1. On the unit Euclidean ball in $\mathbb R^2$, there are linear losses with coefficient norm at most $1$, decisions having interval regret at most $\sqrt{|I|}$ on every interval against every comparator, and a comparator path of length at most $\tau(T)$, while
--      $$\operatorname{D-Reg}_T\ge c_{\rm lin}\tau(T)^{2/5}T^{3/5}.$$
--   2. On the unit $\ell_{3/2}$ ball in $\mathbb R^2$, there are quadratic losses that are $3$-Lipschitz, $1$-strongly convex and $1/9$-exp-concave, decisions having interval regret at most $1$ on every interval against every comparator, and a comparator path of length at most $\tau(T)$, while
--      $$\operatorname{D-Reg}_T\ge c_{\rm quad}\tau(T)^{3/5}T^{2/5}.$$
--
--   This shows that optimal interval regret alone does not imply the minimax dynamic-regret rate on general smooth convex domains.
--
--   Differences from the source:
--   - encoding: "for every sufficiently large $T$ and $\tau=o(T)$" → absolute positive constants followed by every budget function $\tau(T)$ with an eventual lower bound and $\tau(T)/T\to0$, then an eventual quantifier over $T$; reason: little-$o$ is a property of an asymptotic family and the lower-bound constants supplied by the construction are uniform in the budget family
--   - encoding: linear and quadratic losses on the two unit balls → explicit two-dimensional coefficient-norm linear losses and explicit identity-Hessian quadratics together with the printed Lipschitz and curvature predicates; reason: the proof's constructions live in $\mathbb R^2$ and this makes every advertised loss property part of the Lean assertion
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Theorem 1, p.4 (PDF p.6); proof, pp.14–15 (PDF pp.16–17)

import Mathlib
import Definitions.Def_IntervalToDynamic_Supplement_Geometry
import Definitions.Def_LogRegretOCO_ONS_IsExpConcaveOn

open Filter
open ModernOnlineLearning.Dynamic (dynamicRegret pathLength)

namespace IntervalToDynamic.Supplement

/-- Theorem 1 (OIR does not imply ODR on general convex domains), Wang--Zhao--Zhou,
*On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, p.4
(PDF p.6).

Both counterexample families are retained. The positive lower-bound constants are absolute: they
are chosen before the admissible budget family, horizon, losses, decisions, and comparators. -/
theorem theorem_1 :
    ∃ cLin cQuad : ℝ, 0 < cLin ∧ 0 < cQuad ∧
      ∀ tau : ℕ → ℝ,
      (∀ᶠ T in atTop, 1 ≤ tau T) →
      Tendsto (fun T : ℕ => tau T / T) atTop (nhds 0) →
      ∀ᶠ T : ℕ in atTop,
        (∃ (g : ℕ → EuclideanSpace ℝ (Fin 2))
            (x u : ℕ → EuclideanSpace ℝ (Fin 2)),
          (∀ t ∈ Finset.Icc 1 T, ‖g t‖ ≤ 1) ∧
          (∀ t ∈ Finset.Icc 1 T, x t ∈ unitLpBall 2 ∧ u t ∈ unitLpBall 2) ∧
          SatisfiesOIR (T := T) (unitLpBall 2) (fun t z => inner ℝ (g t) z) x 1
            (fun n => Real.sqrt n) ∧
          pathLength u T ≤ tau T ∧
          cLin * tau T ^ (2 / 5 : ℝ) * (T : ℝ) ^ (3 / 5 : ℝ) ≤
            dynamicRegret (fun t z => inner ℝ (g t) z) x u T) ∧
        (∃ (f : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ)
            (a : ℕ → EuclideanSpace ℝ (Fin 2)) (b : ℕ → ℝ)
            (x u : ℕ → EuclideanSpace ℝ (Fin 2)),
          (∀ t ∈ Finset.Icc 1 T, ∀ z,
            f t z = (1 / 2 : ℝ) * ‖z‖ ^ 2 + inner ℝ (a t) z + b t) ∧
          (∀ t ∈ Finset.Icc 1 T, ∀ z ∈ unitLpBall (3 / 2 : ℝ),
            ∀ z' ∈ unitLpBall (3 / 2 : ℝ), |f t z - f t z'| ≤ 3 * ‖z - z'‖) ∧
          (∀ t ∈ Finset.Icc 1 T,
            StrongConvexOn (unitLpBall (3 / 2 : ℝ)) 1 (f t) ∧
            LogRegretOCO.ONS.IsExpConcaveOn (1 / 9 : ℝ) (unitLpBall (3 / 2 : ℝ)) (f t)) ∧
          (∀ t ∈ Finset.Icc 1 T,
            x t ∈ unitLpBall (3 / 2 : ℝ) ∧ u t ∈ unitLpBall (3 / 2 : ℝ)) ∧
          SatisfiesOIR (T := T) (unitLpBall (3 / 2 : ℝ)) f x 1 (fun _ => 1) ∧
          pathLength u T ≤ tau T ∧
          cQuad * tau T ^ (3 / 5 : ℝ) * (T : ℝ) ^ (2 / 5 : ℝ) ≤
            dynamicRegret f x u T) := by sorry

end IntervalToDynamic.Supplement
