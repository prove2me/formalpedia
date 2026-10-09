-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_Deterministic_doob_bound
-- name    : NearlyUnstableHawkes.Deterministic.doob_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:43:32.856988+00:00
-- url     : https://prove2.me/theorems/44c5c997-0d28-476b-ba80-f79eb4d207a2
-- title:
--   §4.1, p. 15 — Doob L² bound for the Hawkes martingale
-- statement:
--   Let $M^T$ be the compensated Hawkes count and assume $\phi^T=a_T\phi$ with $0<a_T<1$. The maximum of its absolute value obeys
--
--   $$\mathbb E\!\left[\sup_{0\le t\le T}|M_t^T|^2\right]\le\frac{4\mu T}{1-a_T}.$$
--
--   The bound combines the $L^2$ maximal inequality with the Hawkes mean estimate and retains the paper's constant $4$.
--
--   **Formalization Note** The source display writes $\sup_t M_t^T$ without absolute value. The absolute-value form is the one needed for the preceding pathwise estimate and follows from the same Doob inequality.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 15, §4.1, Doob inequality display (absolute-value correction)

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_Deterministic_Setting

namespace NearlyUnstableHawkes.Deterministic

open MeasureTheory

/-- Jaisson–Rosenbaum, §4.1, p. 15, outer Doob chain bound. -/
theorem doob_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T μ a m : ℝ) (φ φ' : ℝ → ℝ) (N : ℝ → Ω → ℕ)
    (hT : 0 < T) (hμ : 0 < μ) (ha0 : 0 < a) (ha1 : a < 1)
    (hφ : KernelAssumption φ φ' m)
    (hN : IsHawkes P μ (scaledKernel a φ) T N) :
    (∫⁻ ω, (martingaleMax μ (scaledKernel a φ) N T ω) ^ 2 ∂P) ≤
      ENNReal.ofReal (4 * μ * T / (1 - a)) := by sorry

end NearlyUnstableHawkes.Deterministic
