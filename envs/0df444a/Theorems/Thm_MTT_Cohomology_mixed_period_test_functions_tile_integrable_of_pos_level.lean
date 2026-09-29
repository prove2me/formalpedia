-- Prove2me | Theorems.Thm_MTT_Cohomology_mixed_period_test_functions_tile_integrable_of_pos_level
-- name    : MTT.Cohomology.mixed_period_test_functions_tile_integrable_of_pos_level
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-08T07:21:24.728017+00:00
-- url     : https://prove2.me/theorems/f0601e56-4f52-48c8-ae5a-ba3362c8cf93
-- title:
--   Tile integrability of mixed-period Wirtinger densities at positive level
-- statement:
--   Let $N>0$ and $k\ge 2$. Given cusp forms $g,v,q$ of level $\Gamma_1(N)$ and weight $k$, a mixed-period primitive $U$, and a finite set $R\subseteq\mathrm{SL}_2(\mathbb Z)$, form the two canonical scalar contractions $A_1$ and $A_2$. The Wirtinger derivatives of both functions are integrable over every translated standard modular domain $\sigma\mathcal D$ with $\sigma\in R$.
--
--   The positive-level hypothesis is explicit because the surrounding finite-index quotient argument assumes $N>0$. This theorem supplies the analytic integrability input for the mixed-period Stokes argument.
-- source:
--   Classical mixed Eichler--Shimura period-pairing argument for positive level and weight at least two: contraction identities, cusp-form decay, and finite-index unfolding.

import Definitions.Def_MTT_PeriodPairing
import Mathlib.NumberTheory.ModularForms.Bounds

set_option autoImplicit false
noncomputable section
open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate
open MTT.Cohomology

theorem MTT.Cohomology.mixed_period_test_functions_tile_integrable_of_pos_level
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (g v q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (U : ℂ → Binary ℂ) (hU : IsMixedPeriodPrimitive g v U)
    (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    let A₁ : ℂ → ℂ := fun z =>
      periodContraction (k - 2) (U z)
        (conj ((↑ₕ(fun τ : ℍ ↦ q τ)) z) • periodPower (k - 2) (conj z))
    let A₂ : ℂ → ℂ := fun z => conj <|
      periodContraction (k - 2)
        (((↑ₕ(fun τ : ℍ ↦ q τ)) z) • periodPower (k - 2) z) (U z)
    (∀ σ ∈ R, IntegrableOn
      (fun z ↦ (1 / 2 : ℂ) *
        (fderiv ℝ A₁ z 1 - Complex.I * fderiv ℝ A₁ z Complex.I))
      ((fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟) volume) ∧
    (∀ σ ∈ R, IntegrableOn
      (fun z ↦ (1 / 2 : ℂ) *
        (fderiv ℝ A₂ z 1 - Complex.I * fderiv ℝ A₂ z Complex.I))
      ((fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟) volume) := by sorry
