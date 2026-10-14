-- Prove2me | Theorems.Thm_MFIrrev_Equilibrium_theorem_2_4_ii_tail
-- name    : MFIrrev.Equilibrium.theorem_2_4_ii_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:26.00253+00:00
-- url     : https://prove2.me/theorems/79444f65-84f7-45f2-bd77-ebd6017ebfc1
-- title:
--   Theorem 2.4(ii), p. 7 — the stationary capacity at barriers 0 < a₁ < a₂ has a Pareto tail: P(X∞ ≥ x)/x^{θ₂} → C > 0
-- statement:
--   In the setting of Proposition 4.6 (rates $\delta,\sigma_i>0$, $p_i\in(0,1)$, barriers $0<a_1<a_2$, negative roots $\theta_1<\theta_2<0$ of $\bar\phi$, and the unique solution of (4.31)), let $p_\infty$ be a stationary distribution of the barrier-controlled process $(X^{I^\star}_t,\varepsilon_t)$ and $X_\infty$ its capacity component. Then there is a constant $C>0$ such that
--   $$\lim_{x\to\infty}\frac{\mathbb P(X_\infty\ge x)}{x^{\theta_2}}=C,$$
--   i.e. $\mathbb P(X_\infty\ge x)\sim C\,x^{\theta_2}$.
--
--   The stationary distribution of capacities therefore has a power-law tail with exponent the largest negative root $\theta_2$ of (4.29).
--
--   **Formalization Note.** The page writes $\mathbb P(X^{I^\star}_\infty\ge x)\sim x^{\theta_2}$ without a constant; it is read as convergence of the ratio to a positive constant (by (4.34), $C=-B_2(1-\phi_{12})a_2^{-\theta_2}$). The statement is made for every pair of barriers $0<a_1<a_2$, not only the equilibrium ones, since nothing else is used; the density claim of Theorem 2.4(ii) is Proposition 4.6. "Stationary distribution" is the weak-limit reading of the `Model` definition. Regimes are `Fin 2`.
-- source:
--   Aïd, Basei & Ferrari, A Stationary Mean-Field Equilibrium Model of Irreversible Investment in a Two-Regime Economy, arXiv:2305.00541v1, p. 7, Theorem 2.4(ii) (tail), via (4.34), p. 22

import Mathlib
import Definitions.Def_MFIrrev_Equilibrium_Model

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MFIrrev.Equilibrium

/-- Theorem 2.4(ii), tail part, Aïd–Basei–Ferrari p. 7, read through (4.34): for barriers
`0 < a₁ < a₂` and every stationary distribution `μ` of the barrier-controlled process,
`P(X_∞ ≥ y) ∼ y^{θ₂}` in the sense that `P(X_∞ ≥ y)/y^{θ₂}` converges to a positive constant as
`y → ∞`. -/
theorem theorem_2_4_ii_tail (m : Params) (hδ : 0 < m.δ) (hσ : ∀ j, 0 < m.σ j) (hp : ∀ j, 0 < m.p j ∧ m.p j < 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (S : Setting Ω) (hS : IsSetting m P S)
    (a : Fin 2 → ℝ) (ha0 : 0 < a 0) (ha01 : a 0 < a 1)
    (θ1 θ2 : ℝ) (hθ12 : θ1 < θ2) (hθ2 : θ2 < 0) (hroot1 : phiBar m θ1 = 0) (hroot2 : phiBar m θ2 = 0)
    (A1 A2 B1 B2 : ℝ)
    (hsys : Sys431 m (Real.log (a 0)) (Real.log (a 1)) θ1 θ2 A1 A2 B1 B2)
    (hsys_unique : ∀ A1' A2' B1' B2' : ℝ,
      Sys431 m (Real.log (a 0)) (Real.log (a 1)) θ1 θ2 A1' A2' B1' B2' →
        A1' = A1 ∧ A2' = A2 ∧ B1' = B1 ∧ B2' = B2)
    (x : ℝ) (hx : 0 < x) (i : Fin 2) :
    ∀ μ : Measure (ℝ × Fin 2), HasLimitLaw m P S x i (barrier m S a x) μ →
      ∃ C : ℝ, 0 < C ∧
        Tendsto (fun y : ℝ => (μ {z | y ≤ z.1}).toReal / y ^ θ2) atTop (𝓝 C) := by sorry

end MFIrrev.Equilibrium
