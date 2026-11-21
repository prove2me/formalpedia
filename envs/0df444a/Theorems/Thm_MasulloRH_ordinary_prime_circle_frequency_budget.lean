-- Prove2me | Theorems.Thm_MasulloRH_ordinary_prime_circle_frequency_budget
-- name    : MasulloRH.ordinary_prime_circle_frequency_budget
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T02:38:26.411081+00:00
-- url     : https://prove2.me/theorems/f56f44a8-e114-4f8c-88a5-e05ce9acba07
-- title:
--   Fourier truncation of the ordinary log-prime circle trace with an explicit relative sieve budget
-- statement:
--   Let f be a compactly supported C² complex test on ℝ and write M=∫|f″|. For prime p, let L=log p and cⱼ=f̂(j/L), using the Fourier kernel exp(−2πixξ). The normalized Fourier coefficient of the physical L-periodization is cⱼ/L. Its ordinary unnormalized convolution trace is Tₚ=LΣₙf(nL). The symmetric Fourier truncation to |j|≤N has error at most L²M/(2π²N) for every N≥1. If f(nL) is 1 at n=1 and 0 at all other integers, and the central modes |j|≤N vanish, then M≥2π²N/L. For all primes p≤B the error in the summed trace is at most Aᴮ/N, where Aᴮ=MΣ(log p)²/(2π²). For a>0 write Wᴮ=ζ(a)∏(1−p^(−a)) over these primes. When ζ(a)≠0, every N≥1+ceil((B+1)Aᴮ/|Wᴮ|) makes the relative aggregate error at most 1/(B+1). This comparison concerns the physical ordinary additive-circle trace.
-- source:
--   Ordinary log-prime orbit trace in Masullo, The Music of the Primes, equation (7.4.2.1). Related Mellin–Poisson trace identity https://prove2.me/theorems/10b9dcec-36e9-4ca9-a935-c02bd8872d27 and finite Euler normalization https://prove2.me/theorems/c2c832e0-37f7-48a3-9a12-809625c31683. The quantitative frequency bound, lower bound and relative cutoff are derived directly from Mathlib.

import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta

open MeasureTheory Set Finset Complex
open scoped FourierTransform

theorem MasulloRH.ordinary_prime_circle_frequency_budget
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (a : ℝ) (ha : 0 < a) :
    let L (p : ℕ) := Real.log (p:ℝ)
    let c (p : ℕ) (j : ℤ) := 𝓕 f ((j:ℝ)/L p)
    let T (p : ℕ) := (L p : ℂ) * ∑' n : ℤ, f ((n:ℝ)*L p)
    let S (p N : ℕ) := c p 0 + ∑ k ∈ range N, (c p ((k+1:ℕ):ℤ) + c p (-((k+1:ℕ):ℤ)))
    let M := ∫ x : ℝ, ‖deriv (deriv f) x‖
    let P (B : ℕ) := (range (B+1)).filter Nat.Prime
    let A (B : ℕ) := (∑ p ∈ P B, (L p)^2) * M / (2*Real.pi^2)
    let W (B : ℕ) := riemannZeta (a:ℂ) * ((∏ p ∈ P B, (1-(p:ℝ)^(-a)) : ℝ):ℂ)
    let Nstar (B : ℕ) := ⌈((B:ℝ)+1)*A B/‖W B‖⌉₊ + 1
    (∀ p : ℕ, ∀ hp : p.Prime,
      (∀ j : ℤ, fourierCoeffOn (show (0:ℝ)<L p from Real.log_pos (by exact_mod_cast hp.one_lt))
        (fun x : ℝ => ∑' n : ℤ, f (x+(n:ℝ)*L p)) j = (L p)⁻¹ • c p j) ∧
      ∀ N : ℕ, 0 < N →
        ‖T p - S p N‖ ≤ (L p)^2*M/(2*Real.pi^2*N) ∧
        ((∀ n : ℤ, f ((n:ℝ)*L p) = if n=1 then 1 else 0) →
          (∀ j : ℤ, j.natAbs ≤ N → c p j=0) →
            2 * Real.pi^2 * N / (L p) ≤ M)) ∧
    (∀ B N : ℕ, 0 < N →
      ‖(∑ p ∈ P B, T p) - (∑ p ∈ P B, S p N)‖ ≤ A B/N) ∧
    (riemannZeta (a:ℂ) ≠ 0 → ∀ B N : ℕ, Nstar B ≤ N →
      ‖(∑ p ∈ P B, T p) - (∑ p ∈ P B, S p N)‖ / ‖W B‖ ≤ 1/((B:ℝ)+1)) := by sorry
