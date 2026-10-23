-- Prove2me | Theorems.Thm_JHolomorphic_locallyIntegrable_inv_complex_volume
-- name    : JHolomorphic.locallyIntegrable_inv_complex_volume
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T11:05:34.635405+00:00
-- url     : https://prove2.me/theorems/e77f0abf-d97c-47ca-9564-b4a4745076e0
-- title:
--   The function $1/t$ is locally integrable on $\mathbb C$
-- statement:
--   The function $t\mapsto t^{-1}$ (with $0^{-1}=0$) is locally integrable on $\mathbb C$ with respect to two-dimensional Lebesgue measure.
--
--   **Formalization Note** `LocallyIntegrable (fun t : ℂ => t⁻¹) volume`; Lean's convention `0⁻¹ = 0` fixes the value at the origin, which is a null set.
-- source:
--   Used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Lemma 2.24

import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.Complex.Basic

namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal

/-- The function `t ↦ t⁻¹` on `ℂ` is locally integrable for Lebesgue measure. -/
theorem locallyIntegrable_inv_complex_volume :
    LocallyIntegrable (fun t : ℂ => t⁻¹) volume := by
  sorry

end JHolomorphic
