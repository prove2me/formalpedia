-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianCappedGridUniformLpTwoNormBoundPublic
-- name    : Kyprianou.Ch01.brownianCappedGridUniformLpTwoNormBoundPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:20:41.879054+00:00
-- url     : https://prove2.me/theorems/94017a8f-9374-42f7-a1ca-857485d4602f
-- title:
--   Brownian capped first-crossing stopped exponential grid family has a common finite L2 norm bound
-- statement:
--   For the original drifted Brownian process, positive adjustment root and finite physical horizon, all the sentinel-capped strict first-crossing grid exponentials are almost everywhere strongly measurable and have L2 norms bounded above by a single finite constant independent of grid resolution N. The previously Proved public uniform second-moment estimate for the identical grid provides integrability of each squared exponential and the uniform squared-expectation bound exp(sigma² theta² T), which imply this L2 norm bound. The Proved grid mean-one theorem supplies measurability and first-moment integrability.
-- source:
--   Kyprianou (2006), Exercise 1.10(ii), optional sampling and uniform square-moment control on finite grids.

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianCappedGridUniformLpTwoNormBoundPublic
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q x : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q) (hx : 0 < x)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (T : ℝ≥0) :
    let theta : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    let G : ℕ → Ω → ℝ := fun N ω =>
      let K : ℕ := N + 1
      let delta : ℝ≥0 := T / (K : ℝ≥0)
      let tau : Ω → ℕ := fun ξ => by
        classical
        exact Nat.find (show ∃ k : ℕ,
          k = K ∨ x < X ((k : ℝ≥0) * delta) ξ from ⟨K, Or.inl rfl⟩)
      Real.exp (theta * X ((tau ω : ℝ≥0) * delta) ω -
        q * (((tau ω : ℝ≥0) * delta) : ℝ))
    let tauT : Ω → ℝ≥0 := fun ω =>
      match firstUpperPassage X x ω with
      | none => T
      | some t => min t T
    (∀ N : ℕ, AEStronglyMeasurable (G N) P) ∧
    ∃ C : ℝ≥0, ∀ N : ℕ, eLpNorm (G N) 2 P ≤ (C : ENNReal) := by sorry
