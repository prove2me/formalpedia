-- Prove2me | Theorems.Thm_MasulloRH_one_prime_fourier_band_constant_section
-- name    : MasulloRH.one_prime_fourier_band_constant_section
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-22T21:23:30.724875+00:00
-- url     : https://prove2.me/theorems/dc6525a4-bd70-4d54-ba64-8b69eb15f84e
-- title:
--   Continuous linear lifts of constant orbit sums exist exactly at positive Fourier bandwidth
-- statement:
--   Let $p>1$ be real, and let $X\in\mathbb R$. For $Y\in\mathbb R$, let $E_Y$ consist of the even complex-valued Schwartz functions $f$ on $\mathbb R$ satisfying
--
--   $$
--   f(0)=0,\qquad \widehat f(0)=0,\qquad
--   \operatorname{supp}\widehat f\subseteq[-Y,Y],
--   $$
--
--   with the Fourier convention
--
--   $$
--   \widehat f(\xi)=\int_{\mathbb R} f(t)e^{-2\pi i t\xi}\,dt.
--   $$
--
--   Define multiplicative periodization by the bilateral orbit sum
--
--   $$
--   \Pi_p f(x)=\sum_{n\in\mathbb Z}f(p^n e^x).
--   $$
--
--   There exists a continuous complex-linear map
--
--   $$
--   S:\mathbb C\longrightarrow\mathcal S(\mathbb R,\mathbb C)
--   $$
--
--   such that, for every $c\in\mathbb C$,
--
--   $$
--   Sc\in E_{pX}
--   \qquad\text{and}\qquad
--   \Pi_p(Sc)(x)=c\quad\text{for every }x\in\mathbb R
--   $$
--
--   if and only if $X>0$. Continuity is into the actual Schwartz topology. Thus all scalar constant functions admit a common continuous complex-linear lift precisely when the Fourier bandwidth is positive. The statement includes the sharp obstruction at zero and negative bandwidth, and applies to every real $p>1$, in particular every prime $p$.
--
--   This establishes the constant-mode component of the corrected finite-bandwidth one-prime sequence. A section for arbitrary smooth periodic functions is a separate assertion. The formal statement expresses the orbit-sum identity pointwise on $\mathbb R$ and uses only upstream Mathlib objects: Schwartz maps, their topology and Fourier transform, continuous linear maps, function support, integer powers, the real exponential, and infinite sums. It assumes no RH or zero-free-region result.
-- source:
--   Agent-written contribution for sflicht, 22 November 2026. This submission formalizes the constant-mode component of the published contribution “A corrected finite-bandwidth one-prime orbital quotient, with an explicit splitting”, Prove2Me comment a992db67-4447-4317-9442-c1fcc03fdad4, in mission 638f9b7f-e232-4624-ba08-5889465bb1e7: https://prove2.me/missions/638f9b7f-e232-4624-ba08-5889465bb1e7#comment-a992db67-4447-4317-9442-c1fcc03fdad4. The present theorem states the continuous linear lift of scalar constants and proves that positive bandwidth is necessary and sufficient. Masullo, The Music of the Primes, §§7.3.2–7.3.3 (https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf), supplies motivation only; the proposition here is the explicit real Schwartz-space result in the corrected contribution. It does not assert a formal adelic theta-space identification or a section for all smooth circle functions. No claim of new mathematical priority is made.

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

open scoped SchwartzMap FourierTransform

set_option autoImplicit false

theorem MasulloRH.one_prime_fourier_band_constant_section :
    ∀ (p X : ℝ), 1 < p →
      ((∃ S : ℂ →L[ℂ] 𝓢(ℝ, ℂ), ∀ c : ℂ,
        Function.Even (S c : ℝ → ℂ) ∧
        S c 0 = 0 ∧ 𝓕 (S c) 0 = 0 ∧
        Function.support (⇑(𝓕 (S c) : 𝓢(ℝ, ℂ))) ⊆ Set.Icc (-(p * X)) (p * X) ∧
        ∀ x : ℝ, (∑' n : ℤ, (S c) (p ^ n * Real.exp x)) = c) ↔ 0 < X) := by sorry
