-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_exists_contDiff_periodic_normAtPlace_eq_exp_polarCoord_units_and_fst_eq_and_snd_eq
-- name    : NumberField.mixedEmbedding.exists_contDiff_periodic_normAtPlace_eq_exp_polarCoord_units_and_fst_eq_and_snd_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/d0b432d0-ba4d-5660-9fac-af98aac1b9c4
-- title:
--   Exponential–polar coordinates on the mixed space
-- statement:
--   For a number field $K$, write $V$ for the mixed space $(\{w \text{ real}\}\to\mathbb R)\times(\{w\text{ complex}\}\to\mathbb C)$, and enumerate the infinite places by `Fintype.equivFin` and the complex places likewise. The theorem asserts the existence of a family of maps $P_s\colon \mathbb R^{\#\mathrm{InfinitePlace}\,K}\times\mathbb R^{r_2}\to V$ indexed by sign vectors $s\in(\{w\text{ real}\}\to\mathbb Z^\times)$, together with maps $\mathrm{sgn}\colon V\to(\{w\text{ real}\}\to\mathbb Z^\times)$ and $\arg\colon V\to\mathbb R^{r_2}$, such that: each $P_s$ is $C^\infty$; $P_s(x,\theta+k)=P_s(x,\theta)$ for every integer vector $k\in\mathbb Z^{r_2}$; $P_{ss'}(x+x',\theta+\theta')=P_s(x,\theta)\,P_{s'}(x',\theta')$ in the ring $V$; $\mathrm{normAtPlace}_w(P_s(x,\theta))=\exp(x_w/m_w)$ with $m_w$ the multiplicity of $w$; every unit $y$ of $V$ equals $P_{\mathrm{sgn}\,y}\bigl((m_{w_i}\log\mathrm{normAtPlace}_{w_i}(y))_i,\arg y\bigr)$; for units $y,y'$, $\mathrm{sgn}(yy')=\mathrm{sgn}(y)\,\mathrm{sgn}(y')$ and $\arg(yy')=\arg y+\arg y'+k$ for some $k\in\mathbb Z^{r_2}$; for every compact set $C$ of units there is $R$ with $|x_i|\le R$ for all $i$ whenever $P_s(x,\theta)\in C$. Moreover the chart is explicit: $P_s(x,\theta)_w=s_w\,e^{x_w}$ at a real place $w$, $P_s(x,\theta)_w=\exp(x_w/2+2\pi i\,\theta_w)$ at a complex place, $\mathrm{sgn}(y)_w=1$ if $y_w>0$ and $-1$ otherwise, and $\arg(y)_j=\mathrm{Arg}(y_{w_j})/(2\pi)$.
--
--   This packages Minkowski theory's logarithmic and polar coordinates on the mixed space into a smooth, multiplicative, $\mathbb Z^{r_2}$-periodic parametrisation of the unit group of $V$, with the chart formulas exposed rather than hidden behind the existential quantifier. It is used by [`NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le`](thm.html#NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le), where the archimedean windows must be recognised in exactly these coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_exists_contDiff_periodic_normAtPlace_eq_exp_polarCoord_units_and_fst_eq_and_snd_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

open scoped Classical in

theorem NumberField.mixedEmbedding.exists_contDiff_periodic_normAtPlace_eq_exp_polarCoord_units_and_fst_eq_and_snd_eq
    (K : Type) [Field K] [NumberField K] :
    ∃ (P : ({w : InfinitePlace K // w.IsReal} → ℤˣ) →
          (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin (nrComplexPlaces K) → ℝ) → mixedSpace K)
      (sgn : mixedSpace K → ({w : InfinitePlace K // w.IsReal} → ℤˣ))
      (arg : mixedSpace K → (Fin (nrComplexPlaces K) → ℝ)),
      (∀ s, ContDiff ℝ (⊤ : ℕ∞) (P s)) ∧
      (∀ s (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ)
          (k : Fin (nrComplexPlaces K) → ℤ), P s (x, θ + fun j => (k j : ℝ)) = P s (x, θ)) ∧
      (∀ s s' (x x' : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ θ' : Fin (nrComplexPlaces K) → ℝ),
          P (s * s') (x + x', θ + θ') = P s (x, θ) * P s' (x', θ')) ∧
      (∀ s (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ) (w : InfinitePlace K),
          normAtPlace w (P s (x, θ)) = Real.exp (x (Fintype.equivFin (InfinitePlace K) w) / (w.mult : ℝ))) ∧
      (∀ y : mixedSpace K, IsUnit y →
          P (sgn y) (fun i => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) *
              Real.log (normAtPlace ((Fintype.equivFin (InfinitePlace K)).symm i) y), arg y) = y) ∧
      (∀ y y' : mixedSpace K, IsUnit y → IsUnit y' →
          sgn (y * y') = sgn y * sgn y' ∧
            ∃ k : Fin (nrComplexPlaces K) → ℤ, arg (y * y') = arg y + arg y' + fun j => (k j : ℝ)) ∧
      (∀ C : Set (mixedSpace K), IsCompact C → (∀ y ∈ C, IsUnit y) →
          ∃ R : ℝ, ∀ s (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ),
            P s (x, θ) ∈ C → ∀ i, |x i| ≤ R) ∧
      (∀ s (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ)
          (w : {w : InfinitePlace K // w.IsReal}),
          (P s (x, θ)).1 w = (((s w : ℤˣ) : ℤ) : ℝ) * Real.exp (x (Fintype.equivFin (InfinitePlace K) w.1))) ∧
      (∀ s (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ)
          (w : {w : InfinitePlace K // w.IsComplex}),
          (P s (x, θ)).2 w = Complex.exp (((x (Fintype.equivFin (InfinitePlace K) w.1) / 2 : ℝ) : ℂ) +
            2 * Real.pi * Complex.I * ((θ (Fintype.equivFin {w : InfinitePlace K // w.IsComplex} w) : ℝ) : ℂ))) ∧
      (∀ (y : mixedSpace K) (w : {w : InfinitePlace K // w.IsReal}), sgn y w = if 0 < y.1 w then 1 else -1) ∧
      (∀ (y : mixedSpace K) (j : Fin (nrComplexPlaces K)),
          arg y j = Complex.arg (y.2 ((Fintype.equivFin {w : InfinitePlace K // w.IsComplex}).symm j)) / (2 * Real.pi)) := by sorry
