-- Prove2me | Theorems.Thm_MasterVisc_MKV_lemma_5_14
-- name    : MasterVisc.MKV.lemma_5_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:35:25.363611+00:00
-- url     : https://prove2.me/theorems/a5b80d32-cf61-4e47-9199-12939094a83f
-- title:
--   Lemma 5.14, p. 980 — under Assumption 5.1, V = V₀
-- statement:
--   Let Assumption 5.1 hold. Then the value function $V$ over piecewise constant closed-loop controls (5.3) equals the value function $V_0$ over the controls (5.12) that depend on the past before $t$ only through finitely many observations:
--   $$V(t,\mu)=V_0(t,\mu)\qquad\text{for all }(t,\mu)\in\Theta.$$
--
--   Since $\mathcal A^0_t\subset\mathcal A_t$, the content is $V\le V_0$; with Lemma 5.13 it transfers the continuity of $V_0$ in $\mu$ to $V$.
--
--   **Formalization Note.** The equality is in the extended reals. $A$ is a nonempty Polish space with its Borel $\sigma$-algebra.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), Lemma 5.14, p. 980

import Mathlib
import Definitions.Def_MasterVisc_MKV_Setting
import Definitions.Def_MasterVisc_MKV_Control

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MasterVisc.MKV

/-- Lemma 5.14, p. 980: under Assumption 5.1, `V = V₀`. -/
theorem lemma_5_14 {d : ℕ} {T : ℝ≥0}
    {A : Type} [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
    [Nonempty A]
    (b : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → EthierKurtz.SDEState d)
    (σ : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → ℝ)
    (g : MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → ℝ)
    (C₀ L₀ C : ℝ) (ρ₀ : ℝ → ℝ) (hρ₀ : IsModulus ρ₀)
    (hA : Assumption51 C₀ L₀ ρ₀ C b σ f g) :
    ∀ (t : ℝ≥0) (μ : Measure (MasterVisc.Comparison.Path d T)), t ≤ T → MasterVisc.Comparison.IsP2 μ →
      Vval b σ f g t μ = V0val b σ f g t μ := by sorry

end MasterVisc.MKV
