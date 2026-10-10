-- Prove2me | Theorems.Thm_MasterVisc_MKV_theorem_5_8
-- name    : MasterVisc.MKV.theorem_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:36:15.457035+00:00
-- url     : https://prove2.me/theorems/ee5c11af-89b2-4314-8d05-cf6c006fab85
-- title:
--   Theorem 5.8, p. 972 — under Assumption 5.1, V is a viscosity solution of the HJB master equation (3.22)
-- statement:
--   Let Assumption 5.1 hold, and let $V$ be the value function of the closed-loop McKean–Vlasov control problem (3.18)–(5.3)–(3.20):
--   $$V(t,\mu)=\sup_{\alpha\in\mathcal A_t}\mathbb E^{\mathbb P^{t,\mu,\alpha}}\Big[g(X,\mathbb P^{t,\mu,\alpha})+\int_t^Tf(s,X,\mathbb P^{t,\mu,\alpha},\alpha_s)\,ds\Big].$$
--   Then $V$ is finite on $\Theta$ and is a viscosity solution, in the sense of Definition 4.4, of the HJB master equation
--   $$\partial_tV(t,\mu)+\mathbb E^\mu\Big[\sup_{a\in A}G_2\big(t,\mu,X,\partial_\mu V(t,\mu,X),\partial_\omega\partial_\mu V(t,\mu,X),a\big)\Big]=0,$$
--   where $G_2(t,\mu,\omega,z,\gamma,a)=\tfrac12\gamma:\sigma\sigma^\top(t,\omega,\mu,a)+z\cdot b(t,\omega,\mu,a)+f(t,\omega,\mu,a)$.
--
--   This is the paper's application of its viscosity theory: a path-dependent McKean–Vlasov control problem with closed-loop controls, whose value function is not known to be smooth, is characterized through its HJB master equation.
--
--   **Formalization Note.** The value function is a supremum in the extended reals; the conclusion provides a real-valued $v$ equal to $V$ on $\Theta$ (Definition 4.4 requires $V\in C^0(\Theta)$, so finiteness is part of the claim) and asserts that $v$ is an $L$-viscosity solution for some $L>0$, with test functions as in (4.2). The terminal condition $V(T,\mu)=\mathbb E^\mu[g(X,\mu)]$ of (3.22) is not part of the theorem. $A$ is a nonempty Polish space with its Borel $\sigma$-algebra.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), Theorem 5.8, p. 972, with (3.22), p. 952, and Definition 4.4, p. 959

import Mathlib
import Definitions.Def_MasterVisc_MKV_Setting
import Definitions.Def_MasterVisc_MKV_Viscosity
import Definitions.Def_MasterVisc_MKV_Control

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MasterVisc.MKV

/-- Theorem 5.8, p. 972: under Assumption 5.1, the value function `V` of (3.18)–(5.3)–(3.20) is
finite and is a viscosity solution of the HJB master equation (3.22). -/
theorem theorem_5_8 {d : ℕ} {T : ℝ≥0}
    {A : Type} [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
    [Nonempty A]
    (b : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → EthierKurtz.SDEState d)
    (σ : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → ℝ)
    (g : MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → ℝ)
    (C₀ L₀ C : ℝ) (ρ₀ : ℝ → ℝ) (hρ₀ : IsModulus ρ₀)
    (hA : Assumption51 C₀ L₀ ρ₀ C b σ f g) :
    ∃ v : ℝ≥0 → Measure (MasterVisc.Comparison.Path d T) → ℝ,
      (∀ t μ, t ≤ T → MasterVisc.Comparison.IsP2 μ → Vval b σ f g t μ = v t μ) ∧ IsViscSol (G322 b σ f) v := by sorry

end MasterVisc.MKV
