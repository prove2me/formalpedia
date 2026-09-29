-- Prove2me | Theorems.Thm_NumberField_nonempty_algHom_adicCompletion_of_nontrivial_extension_of_prime
-- name    : NumberField.nonempty_algHom_adicCompletion_of_nontrivial_extension_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/d6af5ec3-c0a5-5e0b-8d87-2b9cd98f2941
-- title:
--   Embedding of L into Kᵥ at a split place
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and suppose the degree $\operatorname{finrank}_K L$ is a prime number. Assume given a $K$-algebra automorphism $\sigma$ of $L$ with $\sigma \neq 1$. Let $v$ be a height-one prime of the ring of integers $\mathcal{O}_K$, and assume: (i) for every height-one prime $w$ of $\mathcal{O}_L$ whose contraction `HeightOneSpectrum.under (𝓞 K) w` equals $v$, the ramification index `Ideal.ramificationIdx'` of $w$ over that contraction is $1$; and (ii) the type of extensions of $v$ to $\mathcal{O}_L$, namely the subtype of height-one primes $w$ of $\mathcal{O}_L$ with `HeightOneSpectrum.under (𝓞 K) w = v`, is `Nontrivial`, i.e. contains at least two distinct elements. The conclusion is that the type of $K$-algebra homomorphisms $L \to$ `v.adicCompletion K`, the $v$-adic completion $K_v$ of $K$, is nonempty: there is a $K$-embedding of $L$ into $K_v$.
--
--   This is the standard fact that a prime of prime-degree cyclic extension which has at least two primes above it splits completely, so that each local extension $L_w/K_v$ is trivial and $L$ embeds $K$-linearly into $K_v$. It supplies the local embedding underlying the split-place coordinates used in the statements about automorphic forms at places with $e = 1$ or $f = 1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_nonempty_algHom_adicCompletion_of_nontrivial_extension_of_prime.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.nonempty_algHom_adicCompletion_of_nontrivial_extension_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hsplit : Nontrivial (v.Extension (𝓞 L))) :
    Nonempty (L →ₐ[K] v.adicCompletion K) := by sorry
