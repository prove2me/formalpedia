-- Prove2me | Theorems.Thm_MeasureTheory_hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable
-- name    : MeasureTheory.hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/2ef6509f-d8d7-5f22-bb7f-c21874efeb6b
-- title:
--   Pointwise Fourier inversion on ℝᶜ for periodic continuous functions
-- statement:
--   Let $c$ be a natural number and let $F\colon(\mathrm{Fin}\,c\to\mathbb R)\to\mathbb C$ be continuous, invariant under translation by each standard basis vector, i.e. $F(\theta+\mathrm{Pi.single}\,j\,1)=F(\theta)$ for all $\theta$ and all coordinates $j$ (so $F$ is $1$-periodic in each variable). For $m\colon\mathrm{Fin}\,c\to\mathbb Z$ put $$\widehat F_m=\int_{\prod_{j}[0,1)}F(\theta')\,\exp\bigl(-2\pi i\textstyle\sum_j m_j\theta'_j\bigr)\,d\theta',$$ the integral being with respect to the Lebesgue measure on $\mathrm{Fin}\,c\to\mathbb R$ over the set $\mathrm{Set.pi}\ \mathrm{Set.univ}\,(\lambda\_,[0,1))$. Assume that $m\mapsto\|\widehat F_m\|$ is summable over $\mathrm{Fin}\,c\to\mathbb Z$. Then for every $\theta\colon\mathrm{Fin}\,c\to\mathbb R$ the family $$m\longmapsto\widehat F_m\cdot\exp\bigl(2\pi i\textstyle\sum_j m_j\theta_j\bigr)$$ is summable with sum $F(\theta)$, in the `HasSum` sense (unconditional convergence of the net of finite partial sums over $\mathrm{Fin}\,c\to\mathbb Z$).
--
--   This is the pointwise Fourier inversion theorem on the $c$-dimensional torus, in the form of absolutely convergent Fourier series of a continuous periodic function on $\mathbb R^c$, stated directly for functions on $\mathbb R^c$ with explicit coordinatewise periodicity rather than for functions on $(\mathbb R/\mathbb Z)^c$. It serves as the reconstruction step in the archimedean window ("kink") computations for automorphic forms, and is cited by the results producing winding data and class-sum expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable
    {c : ℕ} (F : (Fin c → ℝ) → ℂ) (hF : Continuous F)
    (hper : ∀ (θ : Fin c → ℝ) (j : Fin c), F (θ + Pi.single j 1) = F θ)
    (hsum : Summable fun m : Fin c → ℤ =>
      ‖∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
          F θ * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))‖)
    (θ : Fin c → ℝ) :
    HasSum (fun m : Fin c → ℤ =>
      (∫ θ' in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
          F θ' * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ' j : ℝ) : ℂ)))) *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))) (F θ) := by sorry
