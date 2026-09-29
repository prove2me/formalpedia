-- Prove2me | Theorems.Thm_Leopoldt_semilocalGaloisAut_comm_of_exponent_two
-- name    : Leopoldt.semilocalGaloisAut_comm_of_exponent_two
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:43:15.963905+00:00
-- url     : https://prove2.me/theorems/9d6a1135-1a3a-4c01-8a44-4aede8916544
-- title:
--   Commuting semilocal actions of an exponent-two Galois group
-- statement:
--   Let $K/\mathbb Q$ be Galois with all automorphisms of order at most two, and let $p$ be prime. The semilocal actions of any two automorphisms commute:
--   $$\rho_p(\sigma)\rho_p(\tau)=\rho_p(\tau)\rho_p(\sigma).$$
--
--   Together with the involution property, these commuting operators are the algebraic starting point for the simultaneous sign-eigenspace decomposition of semilocal units in the multiquadratic case.
-- source:
--   Functoriality of the semilocal Galois action and the elementary theorem that groups of exponent two are abelian; relevant to the multiquadratic branch of Leopoldt.galois_totallyReal_injection_of_three_le_finrank.

import Definitions.Def_LeopoldtGaloisAction

open NumberField

namespace Leopoldt
theorem semilocalGaloisAut_comm_of_exponent_two (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (h : ∀ ρ : K ≃ₐ[ℚ] K, ρ * ρ = 1) (σ τ : K ≃ₐ[ℚ] K) :
    semilocalGaloisAut p K σ * semilocalGaloisAut p K τ =
      semilocalGaloisAut p K τ * semilocalGaloisAut p K σ := by sorry
end Leopoldt
