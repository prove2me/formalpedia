-- Prove2me | Theorems.Thm_LQGMapII_Kolmogorov_eq_2_10
-- name    : LQGMapII.Kolmogorov.eq_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:43:13.228986+00:00
-- url     : https://prove2.me/theorems/b2eddae6-945e-4dd4-b8e4-e5e826f4cbdb
-- title:
--   (2.10), p. 31 — P[|X_u − X_v| ≥ t2^{−γk}] ≤ c₀t^{−α}2^{−k(d+β−αγ)} for {u, v} ∈ 𝒟̃_k
-- statement:
--   Let $(X_u)_{u \in [0,1]^d}$ be a real random field satisfying (2.6), $\mathbf E|X_u - X_v|^\alpha \le c_0 |u - v|^{d+\beta}$ for all $u, v$, with $\alpha, \beta, c_0 > 0$, and fix $\gamma \in (0, \beta/\alpha)$. For $k \in \mathbb N$ let $\widetilde{\mathcal D}_k$ be the set of pairs of adjacent points of the dyadic grid $\mathcal D_k$ (they differ in one coordinate, by $2^{-k}$). Then for every $k$, every $\{u, v\} \in \widetilde{\mathcal D}_k$ and every $t > 0$,
--   $$
--   \mathbf P\big[|X_u - X_v| \ge t\,2^{-\gamma k}\big] \le c_0\, t^{-\alpha}\, 2^{-k(d+\beta-\alpha\gamma)}. \qquad (2.10)
--   $$
--
--   This is the single-pair estimate at dyadic scale $k$ that the union bounds (2.11) and (2.12) sum over pairs and over scales.
--
--   **Formalization Note** (2.6) is `IsKolmogorovProcess X P α (d + β) c₀` (lower Lebesgue integral in $[0,\infty]$, pairs $(X_u, X_v)$ Borel measurable). The standing assumption $\gamma \in (0, \beta/\alpha)$ of the proof is carried as hypotheses although this display does not need it. $t > 0$ is implicit in the paper and stated. Adjacent pairs are ordered (`IsAdjacentPair d k u v`), and $k$ ranges over $\mathbb N$ including $0$.
-- source:
--   Miller, Sheffield, Liouville quantum gravity and the Brownian map II, Ann. Probab. (2021), DOI 10.1214/21-AOP1506, accepted manuscript, proof of Proposition 2.3, display (2.10), p. 31

import Mathlib
import Definitions.Def_LQGMapII_Kolmogorov_Setting

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LQGMapII.Kolmogorov

/-- (2.10), p. 31: (2.9) at `δ = t 2^{-γk}` for an adjacent pair `{u, v} ∈ 𝒟̃_k`. -/
theorem eq_2_10 {d : ℕ} {α β γ : ℝ} {c₀ : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) (hc₀ : 0 < c₀)
    (hγ : 0 < γ) (hγβ : γ < β / α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Cube d → Ω → ℝ) (hX : IsKolmogorovProcess X P α ((d : ℝ) + β) c₀)
    (k : ℕ) (u v : Cube d) (huv : IsAdjacentPair d k u v) (t : ℝ) (ht : 0 < t) :
    P {ω | t * (2 : ℝ) ^ (-(γ * k)) ≤ |X u ω - X v ω|} ≤
      ENNReal.ofReal ((c₀ : ℝ) * t ^ (-α) * (2 : ℝ) ^ (-((k : ℝ) * ((d : ℝ) + β - α * γ)))) := by sorry

end LQGMapII.Kolmogorov
