-- Prove2me | Theorems.Thm_KingmanSubadditive_Continuous_gamma_limit
-- name    : KingmanSubadditive.Continuous.gamma_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:43:55.112238+00:00
-- url     : https://prove2.me/theorems/a7d2ae9d-63a8-4e2a-9a5b-17208da55eb6
-- title:
--   (1.4.1) — finite continuous-time mean rate and infimum formula
-- statement:
--   Let $x$ be a continuous-parameter subadditive process on a probability space, with finite expected oscillation on some nondegenerate interval $[a,b]\subseteq[0,\infty)$ (separability is not needed here). Write $g_t=E(x_{0t})$ and $\gamma=\inf_{t>0}g_t/t$. Then this infimum is bounded below and
--
--   $$
--   \lim_{t\to\infty}\frac{g_t}{t}=\gamma\in\mathbb R.
--   $$
--
--   This identifies the deterministic mean rate used in the continuous-time limit theorem.
--
--   **Formalization Note** The paper prints (1.4.1) under S₁–S₃ alone. For real time that is false: a non-linear additive Hamel function produces a deterministic subadditive counterexample. The finite-oscillation condition used by Theorem 4 is included here to make the statement valid.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 887, §1.4, (1.4.1); corrected using (1.4.7), p. 889

import Mathlib
import Definitions.Def_KingmanSubadditive_Continuous_Process

namespace KingmanSubadditive.Continuous

open MeasureTheory Filter Topology

/-- Kingman, §1.4, (1.4.1), p. 887. The infimum formula and the real-time limit
are stated under (1.4.7). Formalization Note: S₁–S₃ alone do not imply this
continuous-time limit: a discontinuous additive Hamel function gives a
deterministic counterexample. The local oscillation condition rules it out;
(1.4.7) carries its own a.e. measurability, so separability is not assumed. -/
theorem gamma_limit {S : Type*} [MeasurableSpace S]
    (P : Measure S) [IsProbabilityMeasure P]
    (x : ℝ → ℝ → S → ℝ)
    (hproc : IsProcess P x)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hosc : FiniteOscillation P x (Set.Icc a b)) :
    BddBelow (Set.range (fun t : {t : ℝ // 0 < t} => mean P x t / (t : ℝ))) ∧
      Tendsto (fun t : ℝ => mean P x t / t) atTop (𝓝 (gamma P x)) := by sorry

end KingmanSubadditive.Continuous
