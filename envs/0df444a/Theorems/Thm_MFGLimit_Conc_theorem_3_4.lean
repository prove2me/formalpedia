-- Prove2me | Theorems.Thm_MFGLimit_Conc_theorem_3_4
-- name    : MFGLimit.Conc.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:26:27.08306+00:00
-- url     : https://prove2.me/theorems/158fac83-07f5-467b-82c7-e950fdedda95
-- title:
--   Theorem 3.4, p. 12 — dimension-free concentration of Nash equilibrium paths
-- statement:
--   Assume there is no common-noise coefficient ($\sigma_0=0$). Let $X^1,\ldots,X^n$ be the Nash equilibrium state paths built from a classical solution of the $n$-player Nash system, under Assumption A and either B or B′. Suppose the common initial law $\mu_0$ satisfies (3.7): for some $\kappa>0$, $W_{2,\mathbb R^d}(\mu_0,\nu)\le\sqrt{2\kappa R(\nu\mid\mu_0)}$ for all $\nu\in\mathcal P_2(\mathbb R^d)$ with $\nu\ll\mu_0$. Then constants $C,\delta_1,\delta_2>0$ exist such that, for every $a>0$, positive $n\ge C/a^2$, and 1-Lipschitz $\Phi$ on $((C^d)^n,\|\cdot\|_{n,2})$,
--   $$P\big(\Phi(X)-E\Phi(X)>a\big)\le 2n\exp(-\delta_1 a^2n)+2\exp(-\delta_2a^2).$$
--   The bound combines a population-scale exponential term with a dimension-free path-scale term.
--
--   **Formalization Note** The process family is required to solve (2.7); the classical Nash and master solutions are those of Assumption A. The expectation's integrability is in the conclusion. The action space is Polish, time is $\mathbb R_{\ge0}$, player indices begin at zero, and all constants precede $a,n,\Phi$.
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, p. 12, Theorem 3.4, (3.7)–(3.8)

import Mathlib
import Definitions.Def_MFGLimit_Conc_Transport

namespace MFGLimit.Conc

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Theorem 3.4, equation (3.8): concentration of the Nash state paths without common noise. -/
theorem theorem_3_4 {Ω A : Type*} [mΩ : MeasurableSpace Ω]
    [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A] {d d₀ : ℕ}
    (M : Model Ω A d d₀)
    (v : ∀ n, Fin n → ℝ≥0 → (Fin n → E d) → ℝ)
    (X : ∀ n : ℕ, Fin n → Ω → Path d M.T)
    (hσ₀ : M.σ₀ = 0)
    (hA : AssumptionA M v)
    (hB : AssumptionB M ∨
      ∃ U : ℝ≥0 → E d → Measure (E d) → ℝ,
        IsMasterSolution M U ∧ AssumptionB' M v U)
    (hTransport : ∃ κ : ℝ, TransportIneqPp 2 κ M.μ₀)
    (hX : ∀ n, 1 ≤ n → IsNashState M v (X n)) :
    ∃ C δ₁ δ₂ : ℝ, 0 < C ∧ 0 < δ₁ ∧ 0 < δ₂ ∧
      ∀ a : ℝ, 0 < a → ∀ (n : ℕ), 1 ≤ n → (n : ℝ) ≥ C / a ^ 2 →
      ∀ Φ : Paths2 n d M.T → ℝ, LipschitzWith 1 Φ →
        Integrable (fun ω => Φ (toPaths2 (fun i => X n i ω))) M.P ∧
        M.P {ω | Φ (toPaths2 (fun i => X n i ω)) -
          (∫ ω', Φ (toPaths2 (fun i => X n i ω')) ∂M.P) > a} ≤
          ENNReal.ofReal (2 * (n : ℝ) * Real.exp (-δ₁ * a ^ 2 * (n : ℝ)) +
            2 * Real.exp (-δ₂ * a ^ 2)) := by sorry

end MFGLimit.Conc
