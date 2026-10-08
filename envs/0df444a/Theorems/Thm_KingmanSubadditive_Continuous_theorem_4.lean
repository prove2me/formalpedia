-- Prove2me | Theorems.Thm_KingmanSubadditive_Continuous_theorem_4
-- name    : KingmanSubadditive.Continuous.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:44:46.690985+00:00
-- url     : https://prove2.me/theorems/891d13c4-5b53-4f4c-9b49-47c321e4739f
-- title:
--   Theorem 4 — continuous-parameter subadditive ergodic theorem
-- statement:
--   Let $x=(x_{st})_{0\le s<t}$ be a separable continuous-parameter subadditive process on a probability space. Suppose its expected oscillation is finite on some nondegenerate interval $[a,b]\subseteq[0,\infty)$. Then there is an integrable real random variable $\xi$ for which
--
--   $$
--   \frac{x_{0t}}{t}\longrightarrow\xi
--   \quad\text{almost surely and in }L^1(P)
--   \quad(t\to\infty,\ t\in\mathbb R),
--   \qquad E(\xi)=\gamma=\inf_{u>0}\frac{E(x_{0u})}{u}.
--   $$
--
--   This is Kingman's extension of the discrete subadditive ergodic theorem to all nonnegative real times under a local oscillation condition.
--
--   **Formalization Note** Stationarity is equality of full path laws under every nonnegative real shift. The limit runs over real times, and finite expected oscillation is represented by a nonnegative extended integral.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 889, Theorem 4; (1.4.3), p. 888; (1.4.7), p. 889

import Mathlib
import Definitions.Def_KingmanSubadditive_Continuous_Process

namespace KingmanSubadditive.Continuous

open MeasureTheory Filter Topology

/-- Kingman, Theorem 4, p. 889, with (1.4.3) on p. 888.
Formalization Note: The limit runs through all real times tending to infinity;
separability is graph separability outside one null set, and (1.4.7) is
finite expected oscillation on one nondegenerate interval. -/
theorem theorem_4 {S : Type*} [MeasurableSpace S]
    (P : Measure S) [IsProbabilityMeasure P]
    (x : ℝ → ℝ → S → ℝ)
    (hproc : IsProcess P x) (hsep : IsSeparable P x)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hosc : FiniteOscillation P x (Set.Icc a b)) :
    ∃ ξ : S → ℝ, Integrable ξ P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ => x 0 t ω / t) atTop (𝓝 (ξ ω))) ∧
      Tendsto (fun t : ℝ => ∫ ω, |x 0 t ω / t - ξ ω| ∂P)
        atTop (𝓝 0) ∧
      (∫ ω, ξ ω ∂P) = gamma P x := by sorry

end KingmanSubadditive.Continuous
