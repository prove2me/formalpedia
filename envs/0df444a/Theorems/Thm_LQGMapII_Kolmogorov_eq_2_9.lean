-- Prove2me | Theorems.Thm_LQGMapII_Kolmogorov_eq_2_9
-- name    : LQGMapII.Kolmogorov.eq_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:42:05.623229+00:00
-- url     : https://prove2.me/theorems/fe2c0ba7-4d33-4acd-a2ec-b19810a87449
-- title:
--   (2.9), p. 30 — P[|X_u − X_v| ≥ δ] ≤ c₀δ^{−α}|u − v|^{d+β}
-- statement:
--   Let $(X_u)_{u \in [0,1]^d}$ be a real random field on a probability space $(\Omega, \mathcal F, \mathbf P)$, and let $\alpha, \beta, c_0 > 0$ be constants such that for all $u, v \in [0,1]^d$
--   $$
--   \mathbf E\big[|X_u - X_v|^\alpha\big] \le c_0 |u - v|^{d+\beta}. \qquad (2.6)
--   $$
--   Then for all $u, v \in [0,1]^d$ and every $\delta > 0$,
--   $$
--   \mathbf P\big[|X_u - X_v| \ge \delta\big] \le c_0\, \delta^{-\alpha}\, |u - v|^{d+\beta}. \qquad (2.9)
--   $$
--
--   This is the first step of the proof of Proposition 2.3: Chebyshev's inequality turns the moment bound (2.6) into a tail bound for single increments, which the later steps sum over the dyadic grid.
--
--   **Formalization Note** Hypothesis (2.6) is Mathlib's `IsKolmogorovProcess X P α (d + β) c₀`, which reads (2.6) with the lower Lebesgue integral of $|X_u - X_v|^\alpha$ in $[0,\infty]$ and also requires each pair $(X_u, X_v)$ to be Borel measurable (the paper's "random field"). $|u - v|$ is the Euclidean distance. The condition $\delta > 0$ is implicit in the paper ($\delta^{-\alpha}$ is meaningless at $0$) and is stated.
-- source:
--   Miller, Sheffield, Liouville quantum gravity and the Brownian map II, Ann. Probab. (2021), DOI 10.1214/21-AOP1506, accepted manuscript, proof of Proposition 2.3, display (2.9), p. 30

import Mathlib
import Definitions.Def_LQGMapII_Kolmogorov_Setting

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LQGMapII.Kolmogorov

/-- (2.9), p. 30: Chebyshev's inequality applied to (2.6). -/
theorem eq_2_9 {d : ℕ} {α β : ℝ} {c₀ : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) (hc₀ : 0 < c₀)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Cube d → Ω → ℝ) (hX : IsKolmogorovProcess X P α ((d : ℝ) + β) c₀)
    (u v : Cube d) (δ : ℝ) (hδ : 0 < δ) :
    P {ω | δ ≤ |X u ω - X v ω|} ≤
      ENNReal.ofReal ((c₀ : ℝ) * δ ^ (-α) * dist u v ^ ((d : ℝ) + β)) := by sorry

end LQGMapII.Kolmogorov
