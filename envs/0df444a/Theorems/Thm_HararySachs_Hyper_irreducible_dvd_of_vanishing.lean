-- Prove2me | Theorems.Thm_HararySachs_Hyper_irreducible_dvd_of_vanishing
-- name    : HararySachs.Hyper.irreducible_dvd_of_vanishing
-- status  : Open
-- author  : @milia
-- created : 2026-11-13T05:20:30.322855+00:00
-- url     : https://prove2.me/theorems/6882557a-eab8-4ee9-bcf9-2212a5615d8d
-- title:
--   Nullstellensatz for an irreducible divisor
-- statement:
--   Let $\sigma$ be a finite set and let $g, f \in \mathbb{C}[x_s : s \in \sigma]$ with $g$ irreducible. If $f(x) = 0$ for every point $x \in \mathbb{C}^\sigma$ with $g(x) = 0$, then $g \mid f$.
--
--   By the Nullstellensatz, $f$ lies in the radical of the ideal $(g)$. Since $\mathbb{C}[x]$ is a unique factorization domain, the irreducible $g$ is prime, so $(g)$ is a prime ideal and equals its radical.
--
--   **Formalization Note** Points are functions `σ → ℂ`, and evaluation is `MvPolynomial.eval`.
-- source:
--   Hilbert's Nullstellensatz; Cox, Little, O'Shea, Ideals, Varieties, and Algorithms, Ch. 4. Used in mission strategy comments 8357894d-0c47-45af-94e5-d71263b245a7 and d6dcd7bc-30eb-4f12-bbe1-a5cdf67294f9.

import Mathlib

namespace HararySachs.Hyper

/-- Nullstellensatz for an irreducible polynomial: if `f` vanishes on the zero set of an
irreducible `g`, then `g ∣ f`. -/
theorem irreducible_dvd_of_vanishing {σ : Type*} [Fintype σ] (g f : MvPolynomial σ ℂ)
    (hg : Irreducible g)
    (h : ∀ x : σ → ℂ, MvPolynomial.eval x g = 0 → MvPolynomial.eval x f = 0) : g ∣ f := by
  sorry

end HararySachs.Hyper
