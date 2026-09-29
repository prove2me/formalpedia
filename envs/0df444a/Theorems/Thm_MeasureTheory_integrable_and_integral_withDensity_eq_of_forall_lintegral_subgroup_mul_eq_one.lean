-- Prove2me | Theorems.Thm_MeasureTheory_integrable_and_integral_withDensity_eq_of_forall_lintegral_subgroup_mul_eq_one
-- name    : MeasureTheory.integrable_and_integral_withDensity_eq_of_forall_lintegral_subgroup_mul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/3fb17751-1c1a-576a-ad25-d1fb3aa29d2c
-- title:
--   Independence of int f d(ρμ) from the normalised density ρ
-- statement:
--   Let $G$ be a group with a measurable space structure for which multiplication $G \times G \to G$ is measurable as a function of the pair and inversion is measurable, let $H \le G$ be a subgroup, let $\mu$ be an s-finite left-invariant measure on $G$, and let $\mu_H$ be an s-finite measure on $H$. Let $E$ be a complete normed real vector space. Assume: $\mu_H$ is inversion-invariant in the strong sense that $\int^- f(n^{-1})\,d\mu_H(n) = \int^- f(n)\,d\mu_H(n)$ for every function $f : H \to [0,\infty]$ (no measurability required); $\rho, \rho' : G \to [0,\infty]$ are measurable, take no infinite value, and are normalised along the $H$-orbits in the sense that $\int^-_H \rho(ng)\,d\mu_H(n) = 1$ and $\int^-_H \rho'(ng)\,d\mu_H(n) = 1$ for every $g \in G$; and $f : G \to E$ satisfies $f(ng) = f(g)$ for all $n \in H$, $g \in G$ and is Bochner integrable for the measure $\rho\,d\mu$. The conclusion is the conjunction: $f$ is Bochner integrable for $\rho'\,d\mu$, and $\int_G f\,d(\rho'\mu) = \int_G f\,d(\rho\mu)$.
--
--   This is the Bochner-valued form of the density-independence lemma for left $H$-invariant functions on $G$: the integral of such a function against a density normalised to have total mass $1$ on each coset does not depend on the choice of density, which is the standard device replacing a quotient measure on $H \backslash G$. It is used to replace one normalised density by another in unfolded Rankin–Selberg integrals, in the construction of the integral of a Godement section over the rational centre–unipotent quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_integrable_and_integral_withDensity_eq_of_forall_lintegral_subgroup_mul_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem MeasureTheory.integrable_and_integral_withDensity_eq_of_forall_lintegral_subgroup_mul_eq_one
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (H : Subgroup G) (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] (μH : Measure H) [SFinite μH]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hinv : ∀ f : H → ℝ≥0∞, ∫⁻ n, f n⁻¹ ∂μH = ∫⁻ n, f n ∂μH)
    {ρ ρ' : G → ℝ≥0∞} (hρ : Measurable ρ) (hρ' : Measurable ρ')
    (hρ1 : ∀ g, ∫⁻ n : H, ρ ((n : G) * g) ∂μH = 1) (hρ'1 : ∀ g, ∫⁻ n : H, ρ' ((n : G) * g) ∂μH = 1)
    (hρt : ∀ g, ρ g ≠ ∞) (hρ't : ∀ g, ρ' g ≠ ∞)
    {f : G → E} (hfinv : ∀ (n : H) (g : G), f ((n : G) * g) = f g)
    (hfi : Integrable f (μ.withDensity ρ)) :
    Integrable f (μ.withDensity ρ') ∧
      ∫ g, f g ∂μ.withDensity ρ' = ∫ g, f g ∂μ.withDensity ρ := by sorry
