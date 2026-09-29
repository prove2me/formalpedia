-- Prove2me | Theorems.Thm_MTT_Cohomology_mixed_period_test_functions_wirtinger_data_of_pos_level
-- name    : MTT.Cohomology.mixed_period_test_functions_wirtinger_data_of_pos_level
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-08T07:21:32.084963+00:00
-- url     : https://prove2.me/theorems/d646c8e8-a4eb-4769-9781-07ca47564125
-- title:
--   Wirtinger data for mixed-period test functions at positive level
-- statement:
--   Let $N>0$ and $k\ge 2$. For cusp forms $g,v,q$ of level $\Gamma_1(N)$ and weight $k$, and a mixed-period primitive $U$ for $(g,v)$, there are two scalar test functions $A_1,A_2$ on $\mathbb C$. They are $C^1$ on the upper half-plane, transform with antiholomorphic weight $2$, vanish in every normalized cusp chart, have integrable Wirtinger derivatives on each translated standard tile indexed by a finite set $R$, and their Wirtinger derivatives are the $(g,q)$ period density and minus the conjugate of the $(q,v)$ period density, respectively.
--
--   The hypotheses $N>0$ and $k\ge2$ are the level and weight assumptions used by the main cohomological vanishing theorem.
-- source:
--   Classical mixed Eichler--Shimura period-pairing argument for positive level and weight at least two: contraction identities, cusp-form decay, and finite-index unfolding.

import Definitions.Def_MTT_PeriodPairing
import Mathlib.NumberTheory.ModularForms.Bounds

set_option autoImplicit false
noncomputable section
open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate
open MTT.Cohomology

theorem MTT.Cohomology.mixed_period_test_functions_wirtinger_data_of_pos_level
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (g v q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (U : ℂ → Binary ℂ) (hU : IsMixedPeriodPrimitive g v U)
    (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    ∃ A₁ A₂ : ℂ → ℂ,
      ContDiffOn ℝ 1 A₁ upperHalfPlaneSet ∧
      (∀ γ ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : ℍ,
        A₁ ((γ • τ : ℍ) : ℂ) =
          (starRingEnd ℂ (denom γ τ)) ^ 2 * A₁ τ) ∧
      (∀ σ : Matrix.SpecialLinearGroup (Fin 2) ℤ, IsZeroAtImInfty
        fun τ : ℍ ↦ A₁ ((σ • τ : ℍ) : ℂ) *
          ((starRingEnd ℂ (denom σ τ)) ^ 2)⁻¹) ∧
      (∀ σ ∈ R, IntegrableOn
        (fun z ↦ (1 / 2 : ℂ) *
          (fderiv ℝ A₁ z 1 - Complex.I * fderiv ℝ A₁ z Complex.I))
        ((fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟) volume) ∧
      (∀ z : ℍ,
        (1 / 2 : ℂ) *
            (fderiv ℝ A₁ z 1 - Complex.I * fderiv ℝ A₁ z Complex.I) =
          periodContraction (k - 2)
            (g z • periodPower (k - 2) (z : ℂ))
            (conj (q z) • periodPower (k - 2) (conj (z : ℂ)))) ∧
      ContDiffOn ℝ 1 A₂ upperHalfPlaneSet ∧
      (∀ γ ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : ℍ,
        A₂ ((γ • τ : ℍ) : ℂ) =
          (starRingEnd ℂ (denom γ τ)) ^ 2 * A₂ τ) ∧
      (∀ σ : Matrix.SpecialLinearGroup (Fin 2) ℤ, IsZeroAtImInfty
        fun τ : ℍ ↦ A₂ ((σ • τ : ℍ) : ℂ) *
          ((starRingEnd ℂ (denom σ τ)) ^ 2)⁻¹) ∧
      (∀ σ ∈ R, IntegrableOn
        (fun z ↦ (1 / 2 : ℂ) *
          (fderiv ℝ A₂ z 1 - Complex.I * fderiv ℝ A₂ z Complex.I))
        ((fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟) volume) ∧
      (∀ z : ℍ,
        (1 / 2 : ℂ) *
            (fderiv ℝ A₂ z 1 - Complex.I * fderiv ℝ A₂ z Complex.I) =
          -conj (periodContraction (k - 2)
            (q z • periodPower (k - 2) (z : ℂ))
            (conj (v z) • periodPower (k - 2) (conj (z : ℂ))))) := by sorry
