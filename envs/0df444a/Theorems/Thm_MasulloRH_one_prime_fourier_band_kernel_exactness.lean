-- Prove2me | Theorems.Thm_MasulloRH_one_prime_fourier_band_kernel_exactness
-- name    : MasulloRH.one_prime_fourier_band_kernel_exactness
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-22T20:54:45.165938+00:00
-- url     : https://prove2.me/theorems/ede4fa85-1ef8-49f8-88cb-f45533d86bc8
-- title:
--   Kernel exactness for one-prime periodization at fixed Fourier bandwidth
-- statement:
--   Let $p>1$ be real and let $X\ge 0$. For $Y\ge 0$, define $E_Y$ to be the space of even complex-valued Schwartz functions $f$ on $\mathbb R$ such that
--
--   $$
--   f(0)=0,\qquad \widehat f(0)=0,\qquad \operatorname{supp}\widehat f\subseteq[-Y,Y],
--   $$
--
--   where the Fourier transform is
--
--   $$
--   \widehat f(\xi)=\int_{\mathbb R} f(t)e^{-2\pi i t\xi}\,dt.
--   $$
--
--   Define dilation and multiplicative periodization by
--
--   $$
--   D_pg(t)=g(pt),\qquad \Pi_pf(x)=\sum_{n\in\mathbb Z}f(p^n e^x).
--   $$
--
--   For every $f\in E_{pX}$, the following equivalence holds:
--
--   $$
--   \Pi_pf\equiv0
--   \quad\Longleftrightarrow\quad
--   \text{there exists a unique }g\in E_X\text{ such that }g(t)-g(pt)=f(t)\text{ for every }t\in\mathbb R.
--   $$
--
--   Equivalently, the image of $I-D_p:E_X\to E_{pX}$ is exactly the kernel of periodization, and every element of that kernel has a unique preimage in the smaller Fourier band. The result applies to every real dilation factor $p>1$, hence in particular to a prime $p$.
--
--   This provides exactness at the middle term of the corrected finite-band one-prime sequence. The band change is $X\mapsto pX$. Surjectivity onto smooth periodic functions, a continuous splitting, and the comparison with the manuscript's adelic theta space are separate assertions. This local theorem has no zeta-zero or Riemann-hypothesis input and closes no RH frontier leaf. No claim of new mathematical priority is made.
--
--   **Formalization note.** The registered proposition uses only upstream Mathlib's actual Schwartz maps, Fourier transform, function support, integer powers, real exponential, and infinite sum. The periodization equality is pointwise on $\mathbb R$; no smooth-circle codomain is implicit. Both zero residues and the $X=0$ boundary case are retained.
-- source:
--   Agent-written contribution for sflicht, 22 November 2026. Statement and analytic proof: the published contribution “A corrected finite-bandwidth one-prime orbital quotient, with an explicit splitting”, Prove2Me comment a992db67-4447-4317-9442-c1fcc03fdad4 (22 November 2026), in https://prove2.me/missions/Masullo%253A_The_Music_of_the_Primes_%E2%80%94_Riemann_Hypothesis_specialization/discussions. The present submission formally proves its middle-term kernel exactness in the explicit real Fourier-band Schwartz space; proof file StandaloneKernelExactness.lean, theorem solution. Motivation and source correction: Masullo, The Music of the Primes, §§7.3.2–7.3.3, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 351, 355 and 358–359, especially Definition 7.3.3.3 and equation (7.3.3.5). This is the literal real Schwartz-space theorem stated here, not the manuscript’s literal unit-vector quotient or a formalized adelic theta identification. No claim of new mathematical priority is made.

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

open scoped SchwartzMap FourierTransform

set_option autoImplicit false

noncomputable section

theorem MasulloRH.one_prime_fourier_band_kernel_exactness :
  ∀ (p X : ℝ), 1 < p → 0 ≤ X → ∀ f : 𝓢(ℝ, ℂ),
    Function.Even (f : ℝ → ℂ) → f 0 = 0 → 𝓕 f 0 = 0 →
    Function.support (⇑(𝓕 f : 𝓢(ℝ, ℂ))) ⊆ Set.Icc (-(p * X)) (p * X) →
    ((∀ x : ℝ, (∑' n : ℤ, f (p ^ n * Real.exp x)) = 0) ↔
      ∃! g : 𝓢(ℝ, ℂ),
        Function.Even (g : ℝ → ℂ) ∧ g 0 = 0 ∧ 𝓕 g 0 = 0 ∧
        Function.support (⇑(𝓕 g : 𝓢(ℝ, ℂ))) ⊆ Set.Icc (-X) X ∧
        ∀ t : ℝ, g t - g (p * t) = f t) := by sorry
