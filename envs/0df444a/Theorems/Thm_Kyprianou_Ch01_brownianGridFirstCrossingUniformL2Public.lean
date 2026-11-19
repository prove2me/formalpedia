-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianGridFirstCrossingUniformL2Public
-- name    : Kyprianou.Ch01.brownianGridFirstCrossingUniformL2Public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T10:14:28.122249+00:00
-- url     : https://prove2.me/theorems/00501ee1-1e58-4685-8174-108af5b4db64
-- title:
--   Public fixed-physical-horizon Brownian first crossing exponential uniform L2 estimate
-- statement:
--   At fixed Brownian physical horizon T, choose N positive equal subdivisions delta=T/N and stop at the first grid point strictly above barrier s or at N, whichever comes first. The stopped Brownian adjustment-root exponential has second moment at most exp(sigma² theta² T) independently of N. This is a uniform-integrability estimate in the mesh parameter for the proof of Exercise 1.10(ii).
-- source:
--   Authoritatively accepted private fixed-horizon Brownian L2 proof, reused for public Kyprianou Ch01 Exercise 1.10(ii) convergence.

import Mathlib.Data.NNReal.Defs
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianGridFirstCrossingUniformL2Public
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (sigma gamma q s : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (T : ℝ≥0) (N : ℕ) (hN : 0 < N) :
    let delta : ℝ≥0 := T / (N : ℝ≥0)
    let tau : Ω → ℕ := fun ω => by
      classical
      exact Nat.find (show ∃ k : ℕ,
        k = N ∨ s < X ((k : ℝ≥0) * delta) ω from ⟨N, Or.inl rfl⟩)
    let theta := (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    let M : Ω → ℝ := fun ω =>
      Real.exp (theta * X ((tau ω : ℝ≥0) * delta) ω -
        q * (((tau ω : ℝ≥0) * delta) : ℝ))
    Integrable (fun ω => M ω ^ 2) P ∧
      (∫ ω, M ω ^ 2 ∂P) ≤
        Real.exp (sigma ^ 2 * theta ^ 2 * (T : ℝ)) := by sorry
