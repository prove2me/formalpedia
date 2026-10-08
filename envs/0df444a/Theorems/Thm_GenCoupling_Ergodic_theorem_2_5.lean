-- Prove2me | Theorems.Thm_GenCoupling_Ergodic_theorem_2_5
-- name    : GenCoupling.Ergodic.theorem_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:43.43885+00:00
-- url     : https://prove2.me/theorems/64a0bc71-1555-4f72-b8f0-01c8ebc61743
-- title:
--   Theorem 2.5, p. 9 — Feller + Lyapunov (2.2) + ρ∧1 ≤ θ + Assumption A + B1 on level sets ⇒ unique invariant π and W_{ρ∧1}(P_t(x,·),π) ≤ C₁(1+φ(V(x))^δ)/φ(H_φ^{−1}(C₂t))^δ
-- statement:
--   Let $(E,\rho)$ be a Polish space with its Borel $\sigma$-field, $\{P_t\}_{t\ge0}$ a Feller Markov semigroup on $E$, and $\theta$ a premetric on $E$ (lower semicontinuous, $\theta(x,y)=0\iff x=y$, not necessarily symmetric). Suppose that
--
--   1. there is a measurable $V:E\to[0,\infty)$ satisfying the Lyapunov condition: for a concave differentiable $\varphi:\mathbb R_+\to\mathbb R_+$ increasing to infinity with $\varphi(0)=0$ and a constant $K>0$,
--   $$P_tV(x)\le V(x)-\int_0^tP_s(\varphi\circ V)(x)\,ds+Kt,\qquad t\ge0,\ x\in E;$$
--   2. $\rho\wedge1\le\theta$;
--   3. Assumption A holds for functions $r,L$ (a generalized coupling for every pair of starting points, see the Setting definition);
--   4. there is $t_0>0$ such that for every $M>0$ Assumption B1 holds for $B=\{V\le M\}$ and $t_0$.
--
--   Then $(P_t)$ has a unique invariant probability measure $\pi$. Moreover, for every $\delta\in(0,1)$ there are constants $C_1,C_2>0$ such that for every $x\in E$
--   $$W_{\rho\wedge1}(P_t(x,\cdot),\pi)\le\frac{C_1\bigl(1+\varphi(V(x))^\delta\bigr)}{\varphi\bigl(H_\varphi^{-1}(C_2t)\bigr)^\delta},\qquad t\ge0.\qquad(2.7)$$
--   Here $H_\varphi(x)=\int_1^x du/\varphi(u)$ for $x\ge1$, and $H_\varphi^{-1}(C_2t)$ is the unique $u\ge1$ with $H_\varphi(u)=C_2t$: under condition 1, $\varphi>0$ on $(0,\infty)$ and $\varphi(u)\le\varphi(1)u$ for $u\ge1$, so $H_\varphi$ is a continuous strictly increasing bijection of $[1,\infty)$ onto $[0,\infty)$. $W_{\rho\wedge1}$ is the coupling distance $\inf_{\lambda}\int\rho(x,y)\wedge1\,\lambda(dx,dy)$ over couplings of the two laws.
--
--   This is the paper's unique-ergodicity theorem: a generalized coupling, which only needs to be close in law to the true process, together with a Lyapunov function and a support condition on level sets, gives a unique invariant measure and subexponential convergence in a Wasserstein distance, for Markov processes that need not be strong Feller.
--
--   **Formalization Note** Time is `ℝ≥0`. The semigroup is required to be a Markov transition function with $P_0=\mathrm{id}$, Chapman–Kolmogorov, and (an addition) measurability of $s\mapsto P_s(x,A)$, which (2.2) presupposes; (2.2) is stated in the equivalent subtraction-free form in $[0,\infty]$. In Assumption A, "$\mathrm{Law}(X^{x,y})=\mathsf P_x$" is read through the one-dimensional marginals $\mathrm{Law}(X^{x,y}_t)=P_t(x,\cdot)$, a weaker hypothesis. $H_\varphi^{-1}(C_2t)$ is encoded by quantifying over every $u\ge1$ with $H_\varphi(u)=C_2t$. The constants depend only on $\delta$ (and the data), not on $x$ or $t$. Uniqueness of $\pi$ is among probability measures; the rate is stated for every invariant probability measure, which by uniqueness is $\pi$.
-- source:
--   Butkovsky, Kulik and Scheutzow, Generalized couplings and ergodic rates for SPDEs and other Markov models, arXiv:1806.00395v3, p. 9, Theorem 2.5, (2.7)

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_GenCoupling_Ergodic_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GenCoupling.Ergodic

/-- Theorem 2.5, p. 9: let `P` be a Feller Markov semigroup on a Polish space `(E, ρ)`, `θ` a
premetric, and suppose (1) a measurable `V ≥ 0` satisfies condition 1 of Proposition 2.1,
(2) `ρ ∧ 1 ≤ θ`, (3) Assumption A holds for `r, L`, (4) there is `t₀ > 0` such that for every
`M > 0` Assumption B1 holds for `B = {V ≤ M}` and `t₀`. Then `(P_t)` has a unique invariant
probability measure `π`, and for every `δ ∈ (0,1)` there are `C₁, C₂ > 0` such that (2.7)
`W_{ρ∧1}(P_t(x,·), π) ≤ C₁(1 + φ(V(x))^δ) / φ(H_φ⁻¹(C₂t))^δ` for all `x ∈ E`, `t ≥ 0`; here
`H_φ⁻¹(C₂t)` is the unique `u ≥ 1` with `H_φ(u) = C₂t`. -/
theorem theorem_2_5 {E : Type*} [MetricSpace E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (P : ℝ≥0 → Kernel E E) (hP : IsMarkovSemigroup P) (hF : IsFeller P)
    (θ : E → E → ℝ) (hθ : IsPremetric θ)
    (V : E → ℝ) (hVm : Measurable V) (hV0 : ∀ x, 0 ≤ V x)
    (φ : ℝ → ℝ) (K : ℝ) (h1 : LyapunovCondition P V φ K)
    (h2 : ∀ x y, min (dist x y) 1 ≤ θ x y)
    (r L : ℝ≥0 → ℝ) (h3 : AssumptionA θ P r L)
    (t₀ : ℝ≥0) (h4 : ∀ M : ℝ, 0 < M → AssumptionB1 θ P {x | V x ≤ M} t₀) :
    (∃! π : Measure E, IsProbabilityMeasure π ∧ ∀ t, (P t).Invariant π) ∧
    ∀ π : Measure E, IsProbabilityMeasure π → (∀ t, (P t).Invariant π) →
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
        ∀ (x : E) (t : ℝ≥0) (u : ℝ), 1 ≤ u → H φ u = C₂ * (t : ℝ) →
          W (fun a b => min (dist a b) 1) (P t x) π
            ≤ ENNReal.ofReal (C₁ * (1 + φ (V x) ^ δ) / φ u ^ δ) := by sorry

end GenCoupling.Ergodic
