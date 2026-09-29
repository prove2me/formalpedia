-- Prove2me | Theorems.Thm_FrobeniusDensity_chebotarev_natural_density_core
-- name    : FrobeniusDensity.chebotarev_natural_density_core
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-23T19:29:28.726845+00:00
-- url     : https://prove2.me/theorems/eada4220-79de-4d3b-b51b-db8bd0c3c4a9
-- title:
--   Chebotarev density theorem for Frobenius conjugacy classes
-- statement:
--   For every finite Galois extension of the rationals and every automorphism, the primes whose Frobenius lies in its conjugacy class have density equal to the relative size of that conjugacy class. This remains true after excluding an arbitrary finite set of primes.
-- source:
--   The Chebotarev density theorem; see Neukirch, Algebraic Number Theory, Chapter VII, Section 13. For its use in the present argument, see Kriz–Nordentoft, https://arxiv.org/pdf/2310.20678, Definition 4.1 and the proof of Corollary 4.15. The Frobenius indicator is reused from the Fermat project's Langlands–Tunnell definitions.

import Definitions.Def_LanglandsTunnell_TowerCounting
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

open NumberField Ideal Filter Topology

namespace FrobeniusDensity

/-- Chebotarev's density theorem over `ℚ`, stated as natural density relative to the
rational primes and allowing an arbitrary finite set of excluded residue characteristics. -/
theorem chebotarev_natural_density_core
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
