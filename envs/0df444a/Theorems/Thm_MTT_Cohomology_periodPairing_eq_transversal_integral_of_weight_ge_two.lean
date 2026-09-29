-- Prove2me | Theorems.Thm_MTT_Cohomology_periodPairing_eq_transversal_integral_of_weight_ge_two
-- name    : MTT.Cohomology.periodPairing_eq_transversal_integral_of_weight_ge_two
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-08T07:21:44.403462+00:00
-- url     : https://prove2.me/theorems/0536aa57-b006-40e5-839d-6561b4aff387
-- title:
--   Period pairing as a finite transversal integral in weight at least two
-- statement:
--   Let $k\ge2$, and let $R$ be a finite right transversal for $\Gamma_1(N)$ in $\mathrm{SL}_2(\mathbb Z)$. If an integrable complex density $D$ agrees on the upper half-plane with the period-contraction density attached to cusp forms $f$ and $q$ of weight $k$, then
--
--   $$
--   \langle f,q\rangle_{\mathrm{per}}=\sum_{\sigma\in R}\int_{\sigma\mathcal D}D(z)\,dz.
--   $$
--
--   This is the finite-index unfolding formula used to pass between the quotient definition of the period pairing and translated fundamental domains. The lower bound on $k$ ensures that the symmetric-power degree $k-2$ has the intended weight.
-- source:
--   Classical mixed Eichler--Shimura period-pairing argument for positive level and weight at least two: contraction identities, cusp-form decay, and finite-index unfolding.

import Definitions.Def_MTT_PeriodPairing
import Mathlib.NumberTheory.ModularForms.Bounds

set_option autoImplicit false
noncomputable section
open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate
open MTT.Cohomology

theorem MTT.Cohomology.periodPairing_eq_transversal_integral_of_weight_ge_two
    {N k : ℕ} (hk : 2 ≤ k)
    (f q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hR : Subgroup.IsComplement
      (CongruenceSubgroup.Gamma1 N : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
      (R : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)))
    (D : ℂ → ℂ)
    (hint : ∀ σ ∈ R, IntegrableOn D
      ((fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟) volume)
    (hD : ∀ z : ℍ, D z =
      periodContraction (k - 2)
        (f z • periodPower (k - 2) (z : ℂ))
        (conj (q z) • periodPower (k - 2) (conj (z : ℂ)))) :
    periodPairing N (k - 2) f q =
      ∑ σ ∈ R, ∫ z in (fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟, D z := by sorry
