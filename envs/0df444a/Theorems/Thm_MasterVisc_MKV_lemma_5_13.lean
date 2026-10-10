-- Prove2me | Theorems.Thm_MasterVisc_MKV_lemma_5_13
-- name    : MasterVisc.MKV.lemma_5_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:35:12.610244+00:00
-- url     : https://prove2.me/theorems/e84ed63b-7119-4cf9-836e-bb448347b18d
-- title:
--   Lemma 5.13, p. 977 — V₀ is uniformly continuous in μ, uniformly in t: |V₀(t, μ) − V₀(t, ν)| ≤ ρ(𝒲₂(μ_{[0,t]}, ν_{[0,t]}))
-- statement:
--   Let Assumption 5.1 hold and let $V_0(t,\mu)=\sup_{\alpha\in\mathcal A^0_t}J(t,\mu,\alpha)$ be the value function over the discretely observing controls (5.12). Then there is a modulus of continuity function $\rho$ such that for all $t\in[0,T]$ and $\mu,\nu\in\mathcal P_2$,
--   $$|V_0(t,\mu)-V_0(t,\nu)|\le\rho\big(\mathcal W_2(\mu_{[0,t]},\nu_{[0,t]})\big).\tag{5.15}$$
--
--   Together with Lemma 5.14 this gives the regularity of $V$ in $\mu$.
--
--   **Formalization Note.** $V_0$ takes values in the extended reals; the statement asserts that $V_0(t,\mu)$ and $V_0(t,\nu)$ are real numbers $x,y$ with $|x-y|\le\rho(\cdot)$, since (5.15) subtracts them. $\rho$ is chosen before $t,\mu,\nu$. $A$ is a nonempty Polish space with its Borel $\sigma$-algebra.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), Lemma 5.13, (5.15), p. 977

import Mathlib
import Definitions.Def_MasterVisc_MKV_Setting
import Definitions.Def_MasterVisc_MKV_Control

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MasterVisc.MKV

/-- Lemma 5.13, p. 977: under Assumption 5.1, `V₀` is uniformly continuous in `μ`, uniformly in
`t`: there is a modulus `ρ` with `|V₀(t, μ) − V₀(t, ν)| ≤ ρ(𝒲₂(μ_{[0,t]}, ν_{[0,t]}))` (5.15). -/
theorem lemma_5_13 {d : ℕ} {T : ℝ≥0}
    {A : Type} [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
    [Nonempty A]
    (b : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → EthierKurtz.SDEState d)
    (σ : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → ℝ)
    (g : MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → ℝ)
    (C₀ L₀ C : ℝ) (ρ₀ : ℝ → ℝ) (hρ₀ : IsModulus ρ₀)
    (hA : Assumption51 C₀ L₀ ρ₀ C b σ f g) :
    ∃ ρ : ℝ → ℝ, IsModulus ρ ∧ ∀ (t : ℝ≥0) (μ ν : Measure (MasterVisc.Comparison.Path d T)),
      t ≤ T → MasterVisc.Comparison.IsP2 μ → MasterVisc.Comparison.IsP2 ν →
        ∃ x y : ℝ, V0val b σ f g t μ = x ∧ V0val b σ f g t ν = y ∧
          |x - y| ≤ ρ (W2 (MasterVisc.Comparison.restr t μ) (MasterVisc.Comparison.restr t ν)) := by sorry

end MasterVisc.MKV
