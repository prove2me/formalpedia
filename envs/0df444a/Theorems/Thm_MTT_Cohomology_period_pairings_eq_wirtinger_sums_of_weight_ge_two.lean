-- Prove2me | Theorems.Thm_MTT_Cohomology_period_pairings_eq_wirtinger_sums_of_weight_ge_two
-- name    : MTT.Cohomology.period_pairings_eq_wirtinger_sums_of_weight_ge_two
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-08T07:21:53.60033+00:00
-- url     : https://prove2.me/theorems/9e250f26-5088-414a-8737-d9401b03b06b
-- title:
--   Period pairings as finite Wirtinger sums in weight at least two
-- statement:
--   Let $k\ge2$. Given three cusp forms $g,v,q$ of level $\Gamma_1(N)$ and weight $k$, a finite right transversal $R$, and two integrable Wirtinger densities satisfying the displayed derivative identities, the two period pairings are
--
--   $$
--   \langle g,q\rangle_{\mathrm{per}}=\sum_{\sigma\in R}\int_{\sigma\mathcal D}\partial A_1
--   $$
--
--   and
--
--   $$
--   \langle q,v\rangle_{\mathrm{per}}=-\overline{\sum_{\sigma\in R}\int_{\sigma\mathcal D}\partial A_2}.
--   $$
--
--   This theorem identifies the period pairings with the finite sums to which the Wirtinger form of Stokes' theorem is applied. The hypothesis $k\ge2$ makes explicit the weight range used by the symmetric-power construction.
-- source:
--   Classical mixed Eichler--Shimura period-pairing argument for positive level and weight at least two: contraction identities, cusp-form decay, and finite-index unfolding.

import Definitions.Def_MTT_PeriodPairing
import Mathlib.NumberTheory.ModularForms.Bounds

set_option autoImplicit false
noncomputable section
open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate
open MTT.Cohomology

theorem MTT.Cohomology.period_pairings_eq_wirtinger_sums_of_weight_ge_two
    {N k : ℕ} (hk : 2 ≤ k)
    (g v q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hR : Subgroup.IsComplement
      (CongruenceSubgroup.Gamma1 N : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
      (R : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)))
    {A₁ A₂ : ℂ → ℂ}
    (hint₁ : ∀ σ ∈ R, IntegrableOn
      (fun z ↦ (1 / 2 : ℂ) *
        (fderiv ℝ A₁ z 1 - Complex.I * fderiv ℝ A₁ z Complex.I))
      ((fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟) volume)
    (hint₂ : ∀ σ ∈ R, IntegrableOn
      (fun z ↦ (1 / 2 : ℂ) *
        (fderiv ℝ A₂ z 1 - Complex.I * fderiv ℝ A₂ z Complex.I))
      ((fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟) volume)
    (hderiv₁ : ∀ z : ℍ,
      (1 / 2 : ℂ) *
          (fderiv ℝ A₁ z 1 - Complex.I * fderiv ℝ A₁ z Complex.I) =
        periodContraction (k - 2)
          (g z • periodPower (k - 2) (z : ℂ))
          (conj (q z) • periodPower (k - 2) (conj (z : ℂ))))
    (hderiv₂ : ∀ z : ℍ,
      (1 / 2 : ℂ) *
          (fderiv ℝ A₂ z 1 - Complex.I * fderiv ℝ A₂ z Complex.I) =
        -conj (periodContraction (k - 2)
          (q z • periodPower (k - 2) (z : ℂ))
          (conj (v z) • periodPower (k - 2) (conj (z : ℂ))))) :
    periodPairing N (k - 2) g q =
        ∑ σ ∈ R, ∫ z in (fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟,
          (1 / 2 : ℂ) *
            (fderiv ℝ A₁ z 1 - Complex.I * fderiv ℝ A₁ z Complex.I) ∧
    periodPairing N (k - 2) q v =
        -conj (∑ σ ∈ R, ∫ z in (fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟,
          (1 / 2 : ℂ) *
            (fderiv ℝ A₂ z 1 - Complex.I * fderiv ℝ A₂ z Complex.I)) := by sorry
