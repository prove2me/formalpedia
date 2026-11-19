-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianCappedGridStoppedExponentialL1ConvergencePublic
-- name    : Kyprianou.Ch01.brownianCappedGridStoppedExponentialL1ConvergencePublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T12:15:49.966323+00:00
-- url     : https://prove2.me/theorems/adad3682-dae3-411b-8536-002111166db6
-- title:
--   Brownian first-passage stopped exponential grid converges in L1 over any physical horizon
-- statement:
--   For a drifted Brownian process satisfying the chapter's original Lévy law and almost-sure path continuity, the upper-barrier first-crossing grid-stopped adjustment exponentials on a fixed physical horizon converge to the genuine continuously stopped exponential in L1, with integrable limit. This is the analytic Vitali/uniform-integrability component: establish almost-sure convergence from continuity and shrinking grid mesh, and use the independently Proved uniform L2 bound to obtain uniform integrability.
-- source:
--   Kyprianou (2006), Exercise 1.10(ii), back-of-book solution, stopped exponential first passage and bounded-horizon approximation.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianCappedGridStoppedExponentialL1ConvergencePublic
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
    Integrable (fun ω => Real.exp (theta * X (tauT ω) ω -
      q * (tauT ω : ℝ))) P ∧
    Tendsto (fun N : ℕ =>
      ∫⁻ ω, ‖G N ω - Real.exp (theta * X (tauT ω) ω -
        q * (tauT ω : ℝ))‖ₑ ∂P) atTop (nhds 0) := by sorry
