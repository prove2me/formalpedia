-- Prove2me | Theorems.Thm_MasterVisc_MKV_remark_5_4_i
-- name    : MasterVisc.MKV.remark_5_4_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:35:00.904508+00:00
-- url     : https://prove2.me/theorems/2f046ff2-21d0-4137-b2a1-3949b78ff261
-- title:
--   Remark 5.4(i), p. 970 — for α ∈ 𝒜_t, (3.18) has a unique solution ℙ^{t,μ,α}, and it lies in 𝒫_L(t, μ) for L ≥ C₀ ∨ ½C₀²
-- statement:
--   Let Assumption 5.1 hold with bound $C_0$, let $(t,\mu)\in\Theta$ and let $\alpha\in\mathcal A_t$ be a piecewise constant closed-loop control as in (5.3). Then the controlled McKean–Vlasov equation (3.18) has exactly one solution law $\mathbb P^{t,\mu,\alpha}$, and for every $L$ with
--   $$L\ge C_0\vee\big[\tfrac12C_0^2\big]$$
--   this law belongs to $\mathcal P_L(t,\mu)$.
--
--   This makes $J(t,\mu,\alpha)$ and $V(t,\mu)$ well defined and places all controlled laws in the compact class $\mathcal P_L(t,\mu)$ used by the viscosity theory.
--
--   **Formalization Note.** The control set $A$ is a nonempty Polish space with its Borel $\sigma$-algebra (the paper's "appropriate set $A$"). (3.18) is solved in the weak sense (a representation carrying its own Brownian motion), so the statement is existence and uniqueness of the law; the remark's "(strong)" refers to solvability on a given Brownian space and is not posed. "In particular, $\mathbb P^{t,\mu,\alpha}$ satisfies the uniform estimate (4.1)" is the separate item (4.1) applied to this law.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), Remark 5.4(i), p. 970

import Mathlib
import Definitions.Def_MasterVisc_MKV_Setting
import Definitions.Def_MasterVisc_MKV_Control

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MasterVisc.MKV

/-- Remark 5.4(i), p. 970: under Assumption 5.1, for every `α ∈ 𝒜_t` the controlled equation (3.18)
has a unique solution `ℙ^{t,μ,α}`, and it lies in `𝒫_L(t, μ)` for `L ≥ C₀ ∨ ½C₀²`. -/
theorem remark_5_4_i {d : ℕ} {T : ℝ≥0}
    {A : Type} [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
    [Nonempty A]
    (b : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → EthierKurtz.SDEState d)
    (σ : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → ℝ)
    (g : MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → ℝ)
    (C₀ L₀ C : ℝ) (ρ₀ : ℝ → ℝ) (hρ₀ : IsModulus ρ₀)
    (hA : Assumption51 C₀ L₀ ρ₀ C b σ f g)
    (t : ℝ≥0) (μ : Measure (MasterVisc.Comparison.Path d T)) (ht : t ≤ T) (hμ : MasterVisc.Comparison.IsP2 μ)
    (α : ℝ≥0 → MasterVisc.Comparison.Path d T → A) (hα : IsPWControl t α)
    (L : ℝ) (hL : C₀ ≤ L ∧ C₀ ^ 2 / 2 ≤ L) :
    (∃! P : Measure (MasterVisc.Comparison.Path d T), IsControlledLaw b σ t μ α P) ∧
      ∀ P, IsControlledLaw b σ t μ α P → InPL L t μ P := by sorry

end MasterVisc.MKV
