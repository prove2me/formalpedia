-- Prove2me | Theorems.Thm_MasulloRH_theta_translate_density_of_mertens_bound
-- name    : MasulloRH.theta_translate_density_of_mertens_bound
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:29:52.631173+00:00
-- url     : https://prove2.me/theorems/16054a29-40cd-4795-8087-001dbb739caa
-- title:
--   Rational translates of the dyadic theta are dense above a Mertens exponent, and cofinal finite Gram certificates are equivalent to RH
-- statement:
--   Suppose the summatory Möbius function is O(N^β). On every closed strip with 0 ≤ β < c−b ≤ c+b < 1, finite translates of the actual dyadic theta with rational shifts and Gaussian-rational coefficients approximate every compact continuous target and every normalized Gaussian pulse in the uniform norm with both endpoint weights. These finite sums are dense in L²(exp(2cx+2b|x|) dx), and the closed complex span of the individual rational translates is the entire Hilbert space. Consequently RH is equivalent to existence of the cofinal finite rational Gram certificates of 7c5cdf67, with their prescribed heights, margins and thresholds.
-- source:
--   A. M. Masullo, The Music of the Primes, compact window norm (9.2.2.4), p. 412, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=412. Physical-space Möbius inversion and weighted translate-density argument for the explicit dyadic theta of 714a2f7b. Uses the verified conditional Mertens bound 465491a6 and finite rectangle obstruction 8481aa5d. The cofinal finite approximation property in 7c5cdf67 is still open.

import Definitions.Def_MasulloRH_GaussianThetaApproximation
open Set MeasureTheory Filter Asymptotics
open scoped Topology ENNReal BigOperators
open MasulloRH.GaussianApproximation

theorem MasulloRH.theta_translate_density_of_mertens_bound :
    (∀ β c b : ℝ, 0≤β → 0≤b → β<c-b → c+b<1 →
      (fun n : ℕ => ∑ i ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius i : ℂ)) =O[atTop]
        (fun n : ℕ => (n:ℝ)^β) →
      let μ := volume.withDensity (fun x : ℝ => ENNReal.ofReal (Real.exp (2*c*x+2*b*|x|)))
      let P := fun f : ℝ → ℂ => ∀ ε > (0:ℝ),
        ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ), ∀ x : ℝ,
          max (Real.exp ((c-b)*x)) (Real.exp ((c+b)*x)) *
            ‖f x - ∑ i, (((a i).1:ℂ)+((a i).2:ℂ)*Complex.I)*theta (x-(y i:ℝ))‖ ≤ ε
      (∀ f : ℝ → ℂ, Continuous f → HasCompactSupport f → P f) ∧
      (∀ T : ℝ, 0≤T → P (pulse T)) ∧
      Dense {u : Lp ℂ 2 μ | ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
        (u:ℝ→ℂ) =ᵐ[μ] fun x => ∑ i, (((a i).1:ℂ)+((a i).2:ℂ)*Complex.I)*theta (x-(y i:ℝ))} ∧
      (Submodule.span ℂ {u : Lp ℂ 2 μ | ∃ y : ℚ, (u:ℝ→ℂ) =ᵐ[μ] fun x => theta (x-(y:ℝ))}).topologicalClosure = ⊤) ∧
    (RiemannHypothesis ↔ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
        let δ : ℝ := 1/(16*((n:ℝ)+1))
        energy (3/4) (1/4-δ) (residual n
          (fun i => ((a i).1:ℂ)+((a i).2:ℂ)*Complex.I) (fun i => (y i:ℝ))) <
            δ*Real.exp (-(1/2:ℝ))) := by sorry
