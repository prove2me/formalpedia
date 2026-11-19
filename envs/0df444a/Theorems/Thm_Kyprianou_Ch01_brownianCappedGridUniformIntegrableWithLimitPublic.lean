-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianCappedGridUniformIntegrableWithLimitPublic
-- name    : Kyprianou.Ch01.brownianCappedGridUniformIntegrableWithLimitPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:04:12.884206+00:00
-- url     : https://prove2.me/theorems/25ef8586-6913-4d86-b5ae-417905ecd783
-- title:
--   Fixed-horizon Brownian grid-stopped exponentials are uniformly integrable and the continuous limit is integrable
-- statement:
--   Under exactly the source Brownian law, positive sigma, q, and barrier and measurable coordinates, each fixed-horizon upper first-crossing stopped exponential on a finite uniform grid is almost everywhere strongly measurable; the family across all grids is uniformly integrable in L1; and the continuously capped stopped exponential is integrable. Prove using the independently certified uniform L2 bound for the identical sentinel capped grid, the almost-sure pathwise limit, finite probability measure, and the de la Vallee-Poussin/Vitali criterion. This supplies an independent analytic hypothesis for L1 convergence without assuming the L1 conclusion.
-- source:
--   Kyprianou (2006), Exercise 1.10(ii), back-of-book stopped Brownian exponential first-passage proof, uniform-integrability justification.

import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianCappedGridUniformIntegrableWithLimitPublic
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
    Integrable (fun ω => Real.exp (theta * X (tauT ω) ω -
      q * (tauT ω : ℝ))) P ∧
    UnifIntegrable G 1 P := by sorry
