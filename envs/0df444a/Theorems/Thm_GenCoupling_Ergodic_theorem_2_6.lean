-- Prove2me | Theorems.Thm_GenCoupling_Ergodic_theorem_2_6
-- name    : GenCoupling.Ergodic.theorem_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:01.79463+00:00
-- url     : https://prove2.me/theorems/a8e8fbce-02fd-4ea5-b1c3-9b800044470e
-- title:
--   Theorem 2.6, p. 10 — exponential case φ(x) = γx: condition 4 of Theorem 2.5 can be replaced by B2 on {V ≤ 4K/γ}
-- statement:
--   Let $(E,\rho)$ be a Polish space, $\{P_t\}$ a Feller Markov semigroup on $E$ and $\theta$ a premetric. Suppose that
--
--   1. a measurable $V:E\to[0,\infty)$ satisfies the Lyapunov condition (2.2) with the linear function $\varphi(x)=\gamma x$, $\gamma>0$, and a constant $K>0$;
--   2. $\rho\wedge1\le\theta$;
--   3. Assumption A holds for functions $r,L$;
--
--   4*. Assumption B2 holds for some function $R$, the level set $\{V\le 4K/\gamma\}$ and some $\varepsilon>0$.
--
--   Then $(P_t)$ has a unique invariant probability measure $\pi$, and (2.7) holds: for every $\delta\in(0,1)$ there are $C_1,C_2>0$ such that for all $x\in E$, $t\ge0$,
--   $$W_{\rho\wedge1}(P_t(x,\cdot),\pi)\le\frac{C_1(1+(\gamma V(x))^\delta)}{\bigl(\gamma H_\varphi^{-1}(C_2t)\bigr)^\delta}.$$
--
--   Since $H_\varphi(x)=\gamma^{-1}\log x$, the rate is exponential in $t$; Theorem 4.2 and the SPDE applications of §4 rest on this result.
--
--   **Formalization Note** (2.7) is kept literally with $\varphi(u)=\gamma u$, and $H_\varphi^{-1}(C_2t)$ is encoded as every $u\ge1$ with $H_\varphi(u)=C_2t$. $W_{\rho\wedge1}$ is the coupling distance for $\min(\rho,1)$ with the original metric $\rho$. Generalized couplings are read through one-dimensional marginals (see the Setting definition).
-- source:
--   Butkovsky, Kulik and Scheutzow, Generalized couplings and ergodic rates for SPDEs and other Markov models, arXiv:1806.00395v3, p. 10, Theorem 2.6

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_GenCoupling_Ergodic_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GenCoupling.Ergodic

/-- Theorem 2.6, p. 10: in the exponential case `φ(x) = γx`, `γ > 0`, condition 4 of
Theorem 2.5 can be replaced by 4*: Assumption B2 holds for some `R`, the level set
`{V ≤ 4K/γ}` and some `ε > 0`. Then `(P_t)` has a unique invariant measure `π` and (2.7) holds. -/
theorem theorem_2_6 {E : Type*} [MetricSpace E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (P : ℝ≥0 → Kernel E E) (hP : IsMarkovSemigroup P) (hF : IsFeller P)
    (θ : E → E → ℝ) (hθ : IsPremetric θ)
    (V : E → ℝ) (hVm : Measurable V) (hV0 : ∀ x, 0 ≤ V x)
    (γ : ℝ) (hγ : 0 < γ) (K : ℝ) (h1 : LyapunovCondition P V (fun u => γ * u) K)
    (h2 : ∀ x y, min (dist x y) 1 ≤ θ x y)
    (r L : ℝ≥0 → ℝ) (h3 : AssumptionA θ P r L)
    (R : ℝ≥0 → ℝ) (ε : ℝ) (h4 : AssumptionB2 θ P {x | V x ≤ 4 * K / γ} R ε) :
    (∃! π : Measure E, IsProbabilityMeasure π ∧ ∀ t, (P t).Invariant π) ∧
    ∀ π : Measure E, IsProbabilityMeasure π → (∀ t, (P t).Invariant π) →
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
        ∀ (x : E) (t : ℝ≥0) (u : ℝ), 1 ≤ u → H (fun u => γ * u) u = C₂ * (t : ℝ) →
          W (fun a b => min (dist a b) 1) (P t x) π
            ≤ ENNReal.ofReal (C₁ * (1 + (fun u => γ * u) (V x) ^ δ) / (fun u => γ * u) u ^ δ) := by sorry

end GenCoupling.Ergodic
