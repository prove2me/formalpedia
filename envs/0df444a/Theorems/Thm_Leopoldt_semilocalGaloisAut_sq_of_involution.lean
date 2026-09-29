-- Prove2me | Theorems.Thm_Leopoldt_semilocalGaloisAut_sq_of_involution
-- name    : Leopoldt.semilocalGaloisAut_sq_of_involution
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:32:45.48499+00:00
-- url     : https://prove2.me/theorems/538839d0-d70a-4f01-a533-5b38c2bfcb28
-- title:
--   An involution of a number field acts by an involution on semilocal units
-- statement:
--   Let $K$ be a number field and $p$ a prime. A rational automorphism $\sigma$ of $K$ permutes the primes over $p$ and acts on the product of their local unit groups. If $\sigma^2=1$, then its action on semilocal units also has square one:
--   $$\rho_p(\sigma)^2=1,\qquad \rho_p:\operatorname{Aut}_{\mathbb Q}(K)\to\operatorname{Aut}(U_p(K)).$$
--
--   This gives the involutive operators used to split semilocal units into eigenspaces in the exponent-two Galois case.
-- source:
--   Functoriality of the Galois action on semilocal units, represented by Leopoldt.exists_monoidHom_mulAut_semilocalGaloisAut; relevant to the exponent-two case of Leopoldt.galois_totallyReal_injection_of_three_le_finrank.

import Definitions.Def_LeopoldtGaloisAction

open NumberField

namespace Leopoldt
theorem semilocalGaloisAut_sq_of_involution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] (σ : K ≃ₐ[ℚ] K) (hσ : σ * σ = 1) :
    semilocalGaloisAut p K σ * semilocalGaloisAut p K σ = 1 := by sorry
end Leopoldt
