-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_exists_contDiff_periodic_normAtPlace_eq_exp_div_mult_polarCoord_units
-- name    : NumberField.mixedEmbedding.exists_contDiff_periodic_normAtPlace_eq_exp_div_mult_polarCoord_units
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/feb49f26-27fa-59d1-a2c6-5480e911544f
-- title:
--   Smooth exponential–polar coordinates on mixed-space units
-- statement:
--   Let $K$ be a number field, and write $V$ for its mixed space $\prod_{w \text{ real}}\mathbb{R}\times\prod_{w \text{ complex}}\mathbb{C}$, with $r=\#\{$infinite places$\}$ and $r_2$ the number of complex places. The assertion is the existence of a family of maps $P_s\colon(\mathrm{Fin}\,r\to\mathbb{R})\times(\mathrm{Fin}\,r_2\to\mathbb{R})\to V$, indexed by sign vectors $s$ in the group of maps from the real places of $K$ to $\mathbb{Z}^{\times}$, together with maps $\mathrm{sgn}\colon V\to(\{w\text{ real}\}\to\mathbb{Z}^{\times})$ and $\arg\colon V\to(\mathrm{Fin}\,r_2\to\mathbb{R})$, such that: each $P_s$ is $C^{\infty}$ on $(\mathrm{Fin}\,r\to\mathbb{R})\times(\mathrm{Fin}\,r_2\to\mathbb{R})$; each $P_s$ is invariant under translating the angular variable $\theta$ by an arbitrary integer vector, $P_s(x,\theta+k)=P_s(x,\theta)$ for $k\colon\mathrm{Fin}\,r_2\to\mathbb{Z}$; the family is multiplicative, $P_{ss'}(x+x',\theta+\theta')=P_s(x,\theta)\,P_{s'}(x',\theta')$ in the ring $V$; the moduli are prescribed by the first variable, $\mathrm{normAtPlace}_w(P_s(x,\theta))=\exp\bigl(x_{e(w)}/m_w\bigr)$ for every infinite place $w$, where $e$ is the chosen bijection from the infinite places to $\mathrm{Fin}\,r$ and $m_w$ is the multiplicity of $w$ ($1$ at real, $2$ at complex places); every unit $y$ of $V$ is recovered as $P_{\mathrm{sgn}(y)}\bigl((m_{w}\log\mathrm{normAtPlace}_{w}(y))_{w},\ \arg y\bigr)$, the first entry being read off through $e^{-1}$; on units $\mathrm{sgn}$ is multiplicative and $\arg$ is additive up to an integer vector, i.e. $\mathrm{sgn}(yy')=\mathrm{sgn}(y)\mathrm{sgn}(y')$ and $\arg(yy')=\arg y+\arg y'+k$ for some $k\colon\mathrm{Fin}\,r_2\to\mathbb{Z}$; and finally, for every compact subset $C$ of $V$ all of whose points are units there is a real $R$ with $|x_i|\le R$ for all $i$ whenever $P_s(x,\theta)\in C$.
--
--   This packages exponential–polar coordinates on the unit group $(\mathbb{R}^{\times})^{r_1}\times(\mathbb{C}^{\times})^{r_2}$ of the mixed space, normalised so that the radial variable is the logarithmic embedding $x_w=m_w\log|\cdot|_w$ of Dirichlet's unit theorem. It is used to convert sums and integrals over units of the mixed space, weighted by smooth compactly supported windows, into integrals in the coordinates $(x,\theta)$; the archimedean window and orbital-integral computations for automorphic forms invoke it in this way.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_exists_contDiff_periodic_normAtPlace_eq_exp_div_mult_polarCoord_units.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

open scoped Classical in

theorem NumberField.mixedEmbedding.exists_contDiff_periodic_normAtPlace_eq_exp_div_mult_polarCoord_units
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
            P s (x, θ) ∈ C → ∀ i, |x i| ≤ R) := by sorry
