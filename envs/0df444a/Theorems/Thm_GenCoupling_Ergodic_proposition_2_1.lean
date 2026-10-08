-- Prove2me | Theorems.Thm_GenCoupling_Ergodic_proposition_2_1
-- name    : GenCoupling.Ergodic.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:15.52612+00:00
-- url     : https://prove2.me/theorems/0b2aabdf-a0bb-49ff-b3e1-01e22606915c
-- title:
--   Proposition 2.1, p. 5 (cited) — Feller + Lyapunov (2.2) + ρ∧1 ≤ d + (2.3) on [t₁,t₂] + (2.4) on level sets ⇒ unique π and W_d rate
-- statement:
--   *Cited, not proved in this paper* ([6, Theorem 2.4], [25, Theorem 4.5.2]).
--
--   Let $(E,\rho)$ be a Polish space and $\{P_t\}$ a Feller Markov semigroup on $E$. Suppose there are a measurable $V:E\to[0,\infty)$ and a bounded distance-like function $d$ on $E$ such that:
--
--   1. $V$ satisfies the Lyapunov condition: for a concave differentiable $\varphi:\mathbb R_+\to\mathbb R_+$ increasing to infinity with $\varphi(0)=0$ and a constant $K>0$, $P_tV(x)\le V(x)-\int_0^tP_s(\varphi\circ V)(x)\,ds+Kt$ for all $t\ge0$, $x\in E$ (2.2);
--   2. $\rho\wedge 1\le d$;
--   3. there are $0<t_1<t_2<\infty$ such that $W_d(P_t(x,\cdot),P_t(y,\cdot))\le d(x,y)$ for all $t\in[t_1,t_2]$ and $x,y\in E$ (2.3);
--   4. there is $t>0$ such that for every $M>0$ there is $\varepsilon>0$ with $W_d(P_t(x,\cdot),P_t(y,\cdot))\le(1-\varepsilon)d(x,y)$ for $x,y\in\{V\le M\}$ (2.4).
--
--   Then $(P_t)$ has a unique invariant probability measure $\pi$, and for every $\delta\in(0,1)$ there are $C_1,C_2>0$ such that for all $x\in E$ and $t\ge0$
--   $$W_d(P_t(x,\cdot),\pi)\le\frac{C_1\bigl(1+\varphi(V(x))^\delta\bigr)}{\varphi\bigl(H_\varphi^{-1}(C_2t)\bigr)^\delta},$$
--   where $H_\varphi(x)=\int_1^x du/\varphi(u)$ and $H_\varphi^{-1}(C_2t)$ is the unique $u\ge1$ with $H_\varphi(u)=C_2t$ ($H_\varphi$ is a continuous increasing bijection of $[1,\infty)$ onto $[0,\infty)$ under condition 1).
--
--   This is the abstract convergence theorem that Theorem 2.5 feeds with $d=d_N$.
--
--   **Formalization Note** Condition 2 is stated as $\rho\wedge1\le d$ instead of the page's $\rho\le d$: this is Proposition 2.1 for the complete metric $\rho\wedge1$, which has the same topology and Borel sets, and it is exactly how the proof of Theorem 2.5 invokes it; it is implied by $\rho\le d$. $H_\varphi^{-1}(C_2t)$ is encoded by quantifying over every $u\ge1$ with $H_\varphi(u)=C_2t$. Invariance means $\int P_t(x,\cdot)\,\pi(dx)=\pi$ for all $t$, and uniqueness is among probability measures.
-- source:
--   Butkovsky, Kulik and Scheutzow, Generalized couplings and ergodic rates for SPDEs and other Markov models, arXiv:1806.00395v3, p. 5, Proposition 2.1 (citing [6, Theorem 2.4], [25, Theorem 4.5.2])

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_GenCoupling_Ergodic_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GenCoupling.Ergodic

/-- Proposition 2.1, p. 5 (cited from [6, Theorem 2.4], [25, Theorem 4.5.2]): a Feller
semigroup with a Lyapunov function `V` (condition 1) and a bounded distance-like `d` with
`ρ ∧ 1 ≤ d` (condition 2), (2.3) on `[t₁, t₂]` (condition 3) and (2.4) on every level set
`{V ≤ M}` at one time `t` (condition 4) has a unique invariant probability measure `π`, and for
every `δ ∈ (0,1)` there are `C₁, C₂ > 0` with
`W_d(P_t(x,·), π) ≤ C₁(1 + φ(V(x))^δ) / φ(H_φ⁻¹(C₂t))^δ`. -/
theorem proposition_2_1 {E : Type*} [MetricSpace E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (P : ℝ≥0 → Kernel E E) (hP : IsMarkovSemigroup P) (hF : IsFeller P)
    (V : E → ℝ) (hVm : Measurable V) (hV0 : ∀ x, 0 ≤ V x)
    (d : E → E → ℝ) (hd : IsDistanceLike d) (hdb : ∃ C : ℝ, ∀ x y, d x y ≤ C)
    (φ : ℝ → ℝ) (K : ℝ) (h1 : LyapunovCondition P V φ K)
    (h2 : ∀ x y, min (dist x y) 1 ≤ d x y)
    (h3 : ∃ t₁ t₂ : ℝ≥0, 0 < t₁ ∧ t₁ < t₂ ∧ ∀ t ∈ Set.Icc t₁ t₂, ∀ x y,
      W d (P t x) (P t y) ≤ ENNReal.ofReal (d x y))
    (h4 : ∃ t : ℝ≥0, 0 < t ∧ ∀ M : ℝ, 0 < M → ∃ ε : ℝ, 0 < ε ∧ ∀ x y, V x ≤ M → V y ≤ M →
      W d (P t x) (P t y) ≤ ENNReal.ofReal ((1 - ε) * d x y)) :
    (∃! π : Measure E, IsProbabilityMeasure π ∧ ∀ t, (P t).Invariant π) ∧
    ∀ π : Measure E, IsProbabilityMeasure π → (∀ t, (P t).Invariant π) →
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
        ∀ (x : E) (t : ℝ≥0) (u : ℝ), 1 ≤ u → H φ u = C₂ * (t : ℝ) →
          W d (P t x) π
            ≤ ENNReal.ofReal (C₁ * (1 + φ (V x) ^ δ) / φ u ^ δ) := by sorry

end GenCoupling.Ergodic
