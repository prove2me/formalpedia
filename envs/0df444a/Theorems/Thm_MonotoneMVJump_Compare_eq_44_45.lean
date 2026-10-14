-- Prove2me | Theorems.Thm_MonotoneMVJump_Compare_eq_44_45
-- name    : MonotoneMVJump.Compare.eq_44_45
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:10.914002+00:00
-- url     : https://prove2.me/theorems/3a9cc3ec-ddbe-45d8-9700-41e0aa5970ef
-- title:
--   (44)–(45) — $E[X^{\pi^*}_T]=x-\frac1\theta G(z,t)-\frac1\theta$ and $\mathrm{Var}(X^{\pi^*}_T)=-\frac1{\theta^2}(G(z,t)+1)$
-- statement:
--   Assume the standing market assumptions, the Conditions of Proposition 1, a solution $G$ of (20), initial data $t<T$, $z$ with factor path $Z$, Assumption 1 at $(z,t)$, $\theta>0$, $x\in\mathbb R$, and $R$ solving (38) with $\mathbb E[R_T]\ne1$, $\mathrm{Var}[R_T]>0$. Then an admissible pair $(\pi^*,X^{\pi^*})$ following (39) exists. Every such pair satisfies
--   $$\mathbb E_{x,z,t}[X^{\pi^*}_T]=x-\frac1\theta G(z,t)-\frac1\theta,\qquad \mathrm{Var}_{x,z,t}(X^{\pi^*}_T)=-\frac1{\theta^2}\big[G(z,t)+1\big].$$
--   These are the mean and variance of the optimal terminal wealth, from which the efficient frontier (Theorem 10) follows.
--
--   **Formalization Note** Only the end-to-end equalities of (44) and of the chain (45) are formalized. Assumption 1 is kept from the context of Theorem 10 (p. 29).
-- source:
--   Li, Liang & Pang, Comparison Between Mean-Variance and Monotone Mean-Variance Preferences Under Jump Diffusion and Stochastic Factor Model, arXiv:2211.14473v2, p. 30, proof of Theorem 10, (44)–(45)

import Mathlib
import Definitions.Def_MonotoneMVJump_Compare_PDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MonotoneMVJump.Compare

/-- (44)–(45), proof of Theorem 10 (p. 30): under Assumption 1, a feedback pair of (39) exists in
`ℬ_{x,z,t}`, and for every such pair
`E[X^{π*}_T] = x − (1/θ) G(z, t) − 1/θ` and `Var(X^{π*}_T) = −(1/θ²)(G(z, t) + 1)`. -/
theorem eq_44_45 {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (hM : M.Standing)
    (hP1 : PropOneConditions M) (G : ℝ → ℝ → ℝ) (hG : IsGSolution M G)
    (t : ℝ≥0) (ht : t < M.T) (z : ℝ) (Z : ℝ≥0 → Ω → ℝ) (hZ : M.IsFactor t z Z)
    (hA1 : Assumption1 M G t Z) (θ : ℝ) (hθ : 0 < θ) (x : ℝ) (R : ℝ≥0 → Ω → ℝ)
    (hR : IsRProcess M G t Z R) (hER : ∫ ω, R M.T ω ∂M.P ≠ 1)
    (hVar : 0 < variance (R M.T) M.P) :
    (∃ π X : ℝ≥0 → Ω → ℝ,
        (∀ᵐ ω ∂M.P, ∀ s : ℝ≥0, t ≤ s → s ≤ M.T →
          π s ω = mvStrategy39 M G (Dstar M.P θ x R M.T) Z X s ω) ∧ M.AdmB t x Z π X) ∧
      ∀ π X : ℝ≥0 → Ω → ℝ,
        (∀ᵐ ω ∂M.P, ∀ s : ℝ≥0, t ≤ s → s ≤ M.T →
          π s ω = mvStrategy39 M G (Dstar M.P θ x R M.T) Z X s ω) → M.AdmB t x Z π X →
        ∫ ω, X M.T ω ∂M.P = x - 1 / θ * G z t - 1 / θ ∧
          variance (X M.T) M.P = -(1 / θ ^ 2) * (G z t + 1) := by sorry

end MonotoneMVJump.Compare
