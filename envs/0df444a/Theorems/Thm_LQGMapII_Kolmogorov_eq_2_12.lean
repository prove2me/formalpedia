-- Prove2me | Theorems.Thm_LQGMapII_Kolmogorov_eq_2_12
-- name    : LQGMapII.Kolmogorov.eq_2_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:09.086261+00:00
-- url     : https://prove2.me/theorems/fb7aff6f-ffb2-44f8-a6be-1f732685279e
-- title:
--   (2.12), p. 31 — P[sup_k max_{𝒟̃_k} 2^{γk}|X_u − X_v| ≥ t] ≤ c₂t^{−α}, c₂ uniform
-- statement:
--   Fix $d \in \mathbb N$, constants $\alpha, \beta, c_0 > 0$ and $\gamma \in (0, \beta/\alpha)$. There is a constant $c_2 > 0$ with the following property. For every real random field $(X_u)_{u \in [0,1]^d}$ on a probability space satisfying (2.6), $\mathbf E|X_u - X_v|^\alpha \le c_0 |u - v|^{d+\beta}$ for all $u, v$, and every $t > 0$,
--   $$
--   \mathbf P\Big[\sup_{k \in \mathbb N}\ \max_{\{u,v\} \in \widetilde{\mathcal D}_k} 2^{\gamma k} |X_u - X_v| \ge t\Big] \le c_2\, t^{-\alpha}. \qquad (2.12)
--   $$
--   Here $\widetilde{\mathcal D}_k$ is the set of pairs of adjacent points of the dyadic grid $\mathcal D_k$, and the supremum may be $+\infty$.
--
--   This is the union of (2.11) over all dyadic scales. It controls, with a polynomial tail, the weighted dyadic increments of the field on all scales at once.
--
--   **Formalization Note** The supremum over $k$ and over adjacent pairs is taken in $[0, \infty]$ (an `ℝ≥0∞`-valued `⨆`), so an unbounded family gives $+\infty$ and not a junk value; the event is $\{t \le \sup\}$, not the smaller event "some term is $\ge t$". The constant $c_2$ is chosen before the probability space, the field and $t$; the probability space lives in `Type`. (2.6) is `IsKolmogorovProcess X P α (d + β) c₀`; $t > 0$ is implicit in the paper and stated; $k$ ranges over $\mathbb N$ including $0$.
-- source:
--   Miller, Sheffield, Liouville quantum gravity and the Brownian map II, Ann. Probab. (2021), DOI 10.1214/21-AOP1506, accepted manuscript, proof of Proposition 2.3, display (2.12), p. 31

import Mathlib
import Definitions.Def_LQGMapII_Kolmogorov_Setting

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LQGMapII.Kolmogorov

/-- (2.12), p. 31: tail bound for `sup_k max_{{u,v} ∈ 𝒟̃_k} 2^{γk} |X_u - X_v|`, the supremum
taken in `ℝ≥0∞`. The constant `c₂` is uniform over the field and `t`. -/
theorem eq_2_12 (d : ℕ) (α β γ : ℝ) (c₀ : ℝ≥0) (hα : 0 < α) (hβ : 0 < β) (hc₀ : 0 < c₀)
    (hγ : 0 < γ) (hγβ : γ < β / α) :
    ∃ c₂ : ℝ, 0 < c₂ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Cube d → Ω → ℝ), IsKolmogorovProcess X P α ((d : ℝ) + β) c₀ →
        ∀ t : ℝ, 0 < t →
          P {ω | ENNReal.ofReal t ≤
              ⨆ (k : ℕ) (u : Cube d) (v : Cube d) (_ : IsAdjacentPair d k u v),
                ENNReal.ofReal ((2 : ℝ) ^ (γ * k) * |X u ω - X v ω|)} ≤
            ENNReal.ofReal (c₂ * t ^ (-α)) := by sorry

end LQGMapII.Kolmogorov
