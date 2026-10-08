-- Prove2me | Theorems.Thm_MFGLimit_Conc_theorem_5_4
-- name    : MFGLimit.Conc.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:25:25.500933+00:00
-- url     : https://prove2.me/theorems/001d66b2-2503-498f-a8ad-b9541a92c912
-- title:
--   Theorem 5.4, p. 20 — dimension-free concentration for the interacting system
-- statement:
--   Let $\tilde X=(\tilde X^1,\ldots,\tilde X^n)$ solve the interacting SDE (5.6) without common noise. Its drift satisfies (5.4) with $p=2$ and (5.5), and its i.i.d. initial states have a finite second moment and common law $\tilde\mu_0$ satisfying the quadratic transport inequality (5.8). There is a constant $\delta>0$, independent of $n$, such that for every $a>0$ and 1-Lipschitz $\Phi$ on $((C^d)^n,\|\cdot\|_{n,2})$,
--   $$P\big(\Phi(\tilde X)-E\Phi(\tilde X)>a\big)\le 2e^{-\delta a^2}.$$
--   This is the comparison system's concentration statement needed for the Nash result.
--
--   **Formalization Note** The paths and their expectation are measurable and integrable; this is asserted in the conclusion rather than assumed. The drift uses the same-time reading of (5.4).
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, p. 20, Theorem 5.4, (5.4)–(5.8)

import Mathlib
import Definitions.Def_MFGLimit_Conc_Transport

namespace MFGLimit.Conc

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Theorem 5.4: dimension-free concentration for the interacting system (5.6). -/
theorem theorem_5_4 {Ω : Type*} [mΩ : MeasurableSpace Ω] {d d₀ : ℕ}
    (M : ParticleBase Ω d d₀)
    (btil : ℝ≥0 → E d → Measure (E d) → E d)
    (L : ℝ) (hDrift : IsInteractingDriftWith M 2 L btil)
    (ξ : ℕ → Ω → E d) (μtil : Measure (E d))
    (hInit : IsGenericInitial M ξ μtil)
    (X : ∀ n : ℕ, Fin n → Ω → Path d M.T)
    (hX : ∀ n, 1 ≤ n → IsInteractingSystem M btil
      (fun i => ξ i.val) (X n))
    (hTransport : ∃ κ₀ : ℝ, TransportIneq 2 κ₀ μtil) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ a : ℝ, 0 < a →
      ∀ Φ : Paths2 n d M.T → ℝ, LipschitzWith 1 Φ →
        Integrable (fun ω => Φ (toPaths2 (fun i => X n i ω))) M.P ∧
        M.P {ω | Φ (toPaths2 (fun i => X n i ω)) -
          (∫ ω', Φ (toPaths2 (fun i => X n i ω')) ∂M.P) > a} ≤
          ENNReal.ofReal (2 * Real.exp (-δ * a ^ 2)) := by sorry

end MFGLimit.Conc
