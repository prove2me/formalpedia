-- Prove2me | Theorems.Thm_GenCoupling_Ergodic_proposition_2_2
-- name    : GenCoupling.Ergodic.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:55.13619+00:00
-- url     : https://prove2.me/theorems/a85f18e6-2fd9-4d75-b256-2de2b54358c5
-- title:
--   Proposition 2.2, p. 6 (cited) — with φ(x) = γx, condition 4 of Proposition 2.1 may be replaced by (2.4) on {V ≤ 4K/γ} at one t
-- statement:
--   *Cited, not proved in this paper* ([23, Theorem 4.8]).
--
--   Assume the setting of Proposition 2.1 (a Feller Markov semigroup on a Polish space $(E,\rho)$, measurable $V\ge0$, bounded distance-like $d$ with $\rho\wedge1\le d$, and (2.3) on some $[t_1,t_2]$ with $0<t_1<t_2$), with condition 1 holding for the linear function $\varphi(x)=\gamma x$, $\gamma>0$, and constant $K>0$. Replace condition 4 by the weaker condition
--
--   4*. there exist $\varepsilon>0$, $t>0$ such that $W_d(P_t(x,\cdot),P_t(y,\cdot))\le(1-\varepsilon)d(x,y)$ for all $x,y\in\{V\le 4K/\gamma\}$.
--
--   Then the conclusion of Proposition 2.1 holds: $(P_t)$ has a unique invariant probability measure $\pi$, and for every $\delta\in(0,1)$ there are $C_1,C_2>0$ with
--   $$W_d(P_t(x,\cdot),\pi)\le\frac{C_1(1+(\gamma V(x))^\delta)}{\bigl(\gamma H_\varphi^{-1}(C_2t)\bigr)^\delta},\qquad x\in E,\ t\ge0.$$
--
--   In the exponential case one level set at one time suffices; this is what makes Theorem 2.6 possible.
--
--   **Formalization Note** As in Proposition 2.1: $\rho\wedge1\le d$ for condition 2, and $H_\varphi^{-1}(C_2t)$ encoded as every $u\ge1$ with $H_\varphi(u)=C_2t$. The bound is kept in the literal form of Proposition 2.1 with $\varphi(u)=\gamma u$, not simplified.
-- source:
--   Butkovsky, Kulik and Scheutzow, Generalized couplings and ergodic rates for SPDEs and other Markov models, arXiv:1806.00395v3, p. 6, Proposition 2.2 (citing [23, Theorem 4.8])

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_GenCoupling_Ergodic_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GenCoupling.Ergodic

/-- Proposition 2.2, p. 6 (cited from [23, Theorem 4.8]): if condition 1 of Proposition 2.1
holds with `φ(x) = γx`, `γ > 0`, then condition 4 can be replaced by 4*: for some `ε > 0`,
`t > 0`, (2.4) holds for all `x, y ∈ {V ≤ 4K/γ}`. -/
theorem proposition_2_2 {E : Type*} [MetricSpace E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (P : ℝ≥0 → Kernel E E) (hP : IsMarkovSemigroup P) (hF : IsFeller P)
    (V : E → ℝ) (hVm : Measurable V) (hV0 : ∀ x, 0 ≤ V x)
    (d : E → E → ℝ) (hd : IsDistanceLike d) (hdb : ∃ C : ℝ, ∀ x y, d x y ≤ C)
    (γ : ℝ) (hγ : 0 < γ) (K : ℝ) (h1 : LyapunovCondition P V (fun u => γ * u) K)
    (h2 : ∀ x y, min (dist x y) 1 ≤ d x y)
    (h3 : ∃ t₁ t₂ : ℝ≥0, 0 < t₁ ∧ t₁ < t₂ ∧ ∀ t ∈ Set.Icc t₁ t₂, ∀ x y,
      W d (P t x) (P t y) ≤ ENNReal.ofReal (d x y))
    (h4 : ∃ ε : ℝ, 0 < ε ∧ ∃ t : ℝ≥0, 0 < t ∧ ∀ x y, V x ≤ 4 * K / γ → V y ≤ 4 * K / γ →
      W d (P t x) (P t y) ≤ ENNReal.ofReal ((1 - ε) * d x y)) :
    (∃! π : Measure E, IsProbabilityMeasure π ∧ ∀ t, (P t).Invariant π) ∧
    ∀ π : Measure E, IsProbabilityMeasure π → (∀ t, (P t).Invariant π) →
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
        ∀ (x : E) (t : ℝ≥0) (u : ℝ), 1 ≤ u → H (fun u => γ * u) u = C₂ * (t : ℝ) →
          W d (P t x) π
            ≤ ENNReal.ofReal (C₁ * (1 + (fun u => γ * u) (V x) ^ δ) / (fun u => γ * u) u ^ δ) := by sorry

end GenCoupling.Ergodic
