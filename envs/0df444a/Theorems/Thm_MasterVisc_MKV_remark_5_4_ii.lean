-- Prove2me | Theorems.Thm_MasterVisc_MKV_remark_5_4_ii
-- name    : MasterVisc.MKV.remark_5_4_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:35:37.533006+00:00
-- url     : https://prove2.me/theorems/0355c5df-2053-4ac5-8074-4b8f20a16cb0
-- title:
--   Remark 5.4(ii), p. 970 — under Assumption 5.1, V satisfies the dynamic programming principle (3.21)
-- statement:
--   Let Assumption 5.1 hold and let $V$ be the value function (3.20) with piecewise constant closed-loop controls (5.3). Then for $0\le t_1<t_2\le T$ and $\mu\in\mathcal P_2$,
--   $$V(t_1,\mu)=\sup_{\alpha\in\mathcal A_{t_1}}\Big[V\big(t_2,\mathbb P^{t_1,\mu,\alpha}\big)+\int_{t_1}^{t_2}\mathbb E^{\mathbb P^{t_1,\mu,\alpha}}\big[f(s,X,\mathbb P^{t_1,\mu,\alpha},\alpha_s)\big]ds\Big].$$
--
--   The dynamic programming principle is the only property of $V$ used to derive the viscosity sub- and supersolution properties in Theorem 5.8.
--
--   **Formalization Note.** $V$ takes values in the extended reals; the running-cost term is a real number, so the sum is never of the form $\infty-\infty$. The supremum runs over admissible pairs $(\alpha,\mathbb P^{t_1,\mu,\alpha})$, the law being unique by Remark 5.4(i). $A$ is a nonempty Polish space with its Borel $\sigma$-algebra.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), Remark 5.4(ii), p. 970, with (3.21), p. 952

import Mathlib
import Definitions.Def_MasterVisc_MKV_Setting
import Definitions.Def_MasterVisc_MKV_Control

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MasterVisc.MKV

/-- Remark 5.4(ii), p. 970, with (3.21), p. 952: under Assumption 5.1, `V` satisfies the dynamic
programming principle: for `t₁ < t₂`,
`V(t₁, μ) = sup_{α ∈ 𝒜_{t₁}} [V(t₂, ℙ^{t₁,μ,α}) + ∫_{t₁}^{t₂} 𝔼^{ℙ^{t₁,μ,α}}[f(s, X, ℙ^{t₁,μ,α}, α_s)] ds]`. -/
theorem remark_5_4_ii {d : ℕ} {T : ℝ≥0}
    {A : Type} [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
    [Nonempty A]
    (b : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → EthierKurtz.SDEState d)
    (σ : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → ℝ)
    (g : MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → ℝ)
    (C₀ L₀ C : ℝ) (ρ₀ : ℝ → ℝ) (hρ₀ : IsModulus ρ₀)
    (hA : Assumption51 C₀ L₀ ρ₀ C b σ f g)
    (t₁ t₂ : ℝ≥0) (μ : Measure (MasterVisc.Comparison.Path d T)) (h₁₂ : t₁ < t₂) (h₂ : t₂ ≤ T) (hμ : MasterVisc.Comparison.IsP2 μ) :
    Vval b σ f g t₁ μ =
      ⨆ p : AdmPair b σ t₁ μ, (Vval b σ f g t₂ p.1.2 +
        (((∫ s in (t₁ : ℝ)..(t₂ : ℝ), ∫ ω, f s.toNNReal ω p.1.2 (p.1.1 s.toNNReal ω) ∂p.1.2) : ℝ)
          : EReal)) := by sorry

end MasterVisc.MKV
