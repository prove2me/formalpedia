-- Prove2me | Theorems.Thm_HarrisContact_MeanSize_eq_7_7
-- name    : HarrisContact.MeanSize.eq_7_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:26:50.740681+00:00
-- url     : https://prove2.me/theorems/e31c7b17-069b-4196-a7a0-bdeff9c097a6
-- title:
--   (7.7), p. 982 — first-jump equation for $m_2(t)$ with $K = 2+(4d-2)\lambda$
-- statement:
--   Take death rate $\mu=1$ and linear birth rates $\lambda_k=k\lambda$ with $\lambda\ge0$, on $Z_d$ with $d\ge1$. Let $\xi=\{x,y\}$ be a pair of neighbours, $m_1(t)=m_t(\{x\})$ and $m_2(t)=m_t(\xi)$, and put
--   $$K=2+(4d-2)\lambda,$$
--   the total jump rate out of a pair of neighbours. Then for every $t\ge0$,
--   $$m_2(t)=2e^{-Kt}+K\int_0^t e^{-Ks}\Big\{\frac2K\,m_1(t-s)+\sum_{z\sim\xi}r(\xi,\xi\cup z)\,m_{t-s}(\xi\cup z)\Big\}\,ds,$$
--   where $r$ is the transition matrix of the imbedded jump chain and the sum runs over the sites $z\notin\xi$ adjacent to $\xi$.
--
--   This is the equation obtained by conditioning on the first jump out of $\xi$: with probability $2/K$ one of the two points dies, leaving a singleton, and otherwise a neighbouring site is born. It is the starting point of the bounds (7.9)–(7.11).
--
--   **Formalization Note** The paper's summation variable $x$ is renamed $z$ because $x$ names a point of the pair. The singleton term is written with $\{x\}$; that $\{y\}$ gives the same value is translation invariance. The process is the countable-state chain on finite configurations of §4 (p. 975), with transition function the minimal solution $P_t$ of the backward equations for the rates (4.4)–(4.5); $m_t(\xi)=\sum_\eta P_t(\xi,\eta)\,|\eta|$ is an extended nonnegative real, so a divergent sum is $+\infty$, never $0$.
-- source:
--   Harris (Ann. Probab. 2, 1974), §7, proof of Theorem 7.6, (7.7), p. 982

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.MeanSize

/-- Harris (Ann. Probab. 2, 1974), (7.7), p. 982: for `μ = 1`, `λ_k = kλ`, and a pair of neighbours
`ξ = {x, y}`, the first-jump decomposition
`m_2(t) = 2e^{−Kt} + K ∫_0^t e^{−Ks} {(2/K) m_1(t − s) + Σ'_{z ∼ ξ} r(ξ, ξ ∪ z) m_{t−s}(ξ ∪ z)} ds`
with `K = 2 + (4d − 2)λ`. The page's summation variable `x` is renamed `z`. -/
theorem eq_7_7 {d : ℕ} (hd : 1 ≤ d) (l : ℝ) (hl : 0 ≤ l) (x y : HarrisContact.Extinction.Site d) (hxy : y ∈ HarrisContact.Extinction.nbrs x)
    (t : ℝ) (ht : 0 ≤ t) :
    HarrisContact.Extinction.meanSize 1 (fun k => (k : ℝ) * l) t ({x, y} : HarrisContact.Extinction.Config d) =
      2 * ENNReal.ofReal (Real.exp (-((2 + (4 * (d : ℝ) - 2) * l) * t))) +
      ∫⁻ s in Set.Icc 0 t,
        ENNReal.ofReal ((2 + (4 * (d : ℝ) - 2) * l) * Real.exp (-((2 + (4 * (d : ℝ) - 2) * l) * s))) *
          (ENNReal.ofReal (2 / (2 + (4 * (d : ℝ) - 2) * l)) *
              HarrisContact.Extinction.meanSize 1 (fun k => (k : ℝ) * l) (t - s) {x} +
            ∑ z ∈ HarrisContact.Extinction.bdry ({x, y} : HarrisContact.Extinction.Config d),
              ENNReal.ofReal (HarrisContact.Extinction.jump 1 (fun k => (k : ℝ) * l) {x, y} (insert z {x, y})) *
                HarrisContact.Extinction.meanSize 1 (fun k => (k : ℝ) * l) (t - s) (insert z {x, y})) := by sorry
end HarrisContact.MeanSize
