-- Prove2me | Theorems.Thm_FrobeniusDensity_chebotarev_natural_density
-- name    : FrobeniusDensity.chebotarev_natural_density
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-18T06:30:17.214666+00:00
-- url     : https://prove2.me/theorems/4b65e18d-7194-47f0-ab43-d429b9b0410b
-- title:
--   Chebotarev natural density for a Frobenius conjugacy class
-- statement:
--   **This is a formalization of a standard textbook result, so should be low-priority**
--
--   Let $L/\mathbf Q$ be a finite Galois extension, let $\sigma\in\operatorname{Gal}(L/\mathbf Q)$, and let $S$ be any finite set of rational residue characteristics. Among rational primes $\ell<X$, count those outside $S$ which are unramified in $L$ and whose arithmetic Frobenius conjugacy class is the conjugacy class of $\sigma$. The ratio of this count to the number of all rational primes below $X$ tends to
--
--   $$
--   \frac{|[\sigma]|}{|\operatorname{Gal}(L/\mathbf Q)|}.
--   $$
--
--   Here the numerator is expressed using `LanglandsTunnell.classIndicator`: it is one precisely when there is a prime above $\ell$ with trivial inertia and arithmetic Frobenius conjugate to $\sigma$. The finite exceptional set permits simultaneous avoidance of bad reduction, conductors, and other prescribed local conditions in the orderly-prime construction.
-- source:
--   The Chebotarev density theorem; see Neukirch, Algebraic Number Theory, Chapter VII, Section 13. For its use in the present argument, see Kriz–Nordentoft, https://arxiv.org/pdf/2310.20678, Definition 4.1 and the proof of Corollary 4.15. The Frobenius indicator is reused from the Fermat project's Langlands–Tunnell definitions.

import Definitions.Def_LanglandsTunnell_TowerCounting
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

open NumberField Ideal Filter Topology

namespace FrobeniusDensity

/-- Chebotarev's density theorem over `ℚ`, stated as natural density relative to the
rational primes and allowing an arbitrary finite set of excluded residue characteristics. -/
theorem chebotarev_natural_density
    (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (σ : L ≃ₐ[ℚ] L) (S : Finset ℕ) :
    Tendsto
      (fun X : ℕ =>
        (((Finset.range X).filter fun ℓ =>
            ℓ ∉ S ∧ LanglandsTunnell.classIndicator σ ℓ = 1).card : ℝ) /
          (((Finset.range X).filter Nat.Prime).card : ℝ))
      atTop
      (𝓝 ((Nat.card {τ : L ≃ₐ[ℚ] L | IsConj σ τ} : ℝ) /
        (Nat.card (L ≃ₐ[ℚ] L) : ℝ))) := by sorry

end FrobeniusDensity
