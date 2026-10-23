-- Prove2me | Theorems.Thm_JHolomorphic_integrable_inv_sub_smul_of_continuous
-- name    : JHolomorphic.integrable_inv_sub_smul_of_continuous
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T10:04:18.490025+00:00
-- url     : https://prove2.me/theorems/3ceecc0d-5790-4bf8-9b40-c95ab671cd0b
-- title:
--   The Cauchy integrand of a continuous compactly supported function is integrable
-- statement:
--   Let $E$ be a complex normed space and $g:\mathbb C\to E$ continuous with compact support. For every $z\in\mathbb C$ the function $\zeta\mapsto (z-\zeta)^{-1}g(\zeta)$ is Lebesgue integrable on $\mathbb C$, so the Cauchy transform of $g$ is defined by a genuinely convergent integral at every point.
--
--   **Formalization Note** `Integrable (fun ζ => (z - ζ)⁻¹ • g ζ)` with respect to `volume` on `ℂ`.
-- source:
--   Used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Lemma 2.24

import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Convolution

/-- For a continuous compactly supported `g : ℂ → E` and any `z`, the map `ζ ↦ (z - ζ)⁻¹ • g ζ` is integrable. -/
theorem integrable_inv_sub_smul_of_continuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {g : ℂ → E} (hg : Continuous g) (hgc : HasCompactSupport g) (z : ℂ) :
    Integrable (fun ζ => (z - ζ)⁻¹ • g ζ) := by
  sorry

end JHolomorphic
