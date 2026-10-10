-- Prove2me | Theorems.Thm_LQGMapII_Kolmogorov_eq_2_11
-- name    : LQGMapII.Kolmogorov.eq_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:34.983339+00:00
-- url     : https://prove2.me/theorems/ce77c756-ba62-40e0-a9b0-06188cae5b21
-- title:
--   (2.11), p. 31 — P[max_{𝒟̃_k} |X_u − X_v| ≥ t2^{−γk}] ≤ c₁t^{−α}2^{−k(β−αγ)}, c₁ uniform
-- statement:
--   Fix $d \in \mathbb N$, constants $\alpha, \beta, c_0 > 0$ and $\gamma \in (0, \beta/\alpha)$. There is a constant $c_1 > 0$ with the following property. For every real random field $(X_u)_{u \in [0,1]^d}$ on a probability space satisfying (2.6), $\mathbf E|X_u - X_v|^\alpha \le c_0 |u - v|^{d+\beta}$ for all $u, v$, for every $k \in \mathbb N$ and every $t > 0$,
--   $$
--   \mathbf P\Big[\max_{\{u,v\} \in \widetilde{\mathcal D}_k} |X_u - X_v| \ge t\,2^{-\gamma k}\Big] \le c_1\, t^{-\alpha}\, 2^{-k(\beta-\alpha\gamma)}, \qquad (2.11)
--   $$
--   where $\widetilde{\mathcal D}_k$ is the set of pairs of adjacent points of the dyadic grid $\mathcal D_k$.
--
--   Since $|\widetilde{\mathcal D}_k| = O(2^{dk})$, this is the union of the single-pair bounds (2.10) over one dyadic scale.
--
--   **Formalization Note** The constant $c_1$ is chosen before the probability space, the field, $k$ and $t$: it depends only on $d, \alpha, \beta, \gamma, c_0$. It is **not** the $c_1$ of (2.8); the paper reuses the name. The maximum over the finite set $\widetilde{\mathcal D}_k$ is attained, so the event is written as "some adjacent pair $(u, v)$ of level $k$ has $t\,2^{-\gamma k} \le |X_u - X_v|$" (this also covers $d = 0$, where $\widetilde{\mathcal D}_k$ is empty). The probability space lives in `Type` (universe 0) so that the constant is a single number. (2.6) is `IsKolmogorovProcess X P α (d + β) c₀`; $t > 0$ is implicit in the paper and stated.
-- source:
--   Miller, Sheffield, Liouville quantum gravity and the Brownian map II, Ann. Probab. (2021), DOI 10.1214/21-AOP1506, accepted manuscript, proof of Proposition 2.3, display (2.11), p. 31

import Mathlib
import Definitions.Def_LQGMapII_Kolmogorov_Setting

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LQGMapII.Kolmogorov

/-- (2.11), p. 31: union bound over `𝒟̃_k`. The constant `c₁` (not the `c₁` of (2.8)) is
uniform over the field, the level `k` and `t`. -/
theorem eq_2_11 (d : ℕ) (α β γ : ℝ) (c₀ : ℝ≥0) (hα : 0 < α) (hβ : 0 < β) (hc₀ : 0 < c₀)
    (hγ : 0 < γ) (hγβ : γ < β / α) :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Cube d → Ω → ℝ), IsKolmogorovProcess X P α ((d : ℝ) + β) c₀ →
        ∀ (k : ℕ) (t : ℝ), 0 < t →
          P {ω | ∃ u v, IsAdjacentPair d k u v ∧ t * (2 : ℝ) ^ (-(γ * k)) ≤ |X u ω - X v ω|} ≤
            ENNReal.ofReal (c₁ * t ^ (-α) * (2 : ℝ) ^ (-((k : ℝ) * (β - α * γ)))) := by sorry

end LQGMapII.Kolmogorov
