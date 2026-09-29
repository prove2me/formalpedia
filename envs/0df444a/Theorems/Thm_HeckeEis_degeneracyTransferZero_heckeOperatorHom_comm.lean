-- Prove2me | Theorems.Thm_HeckeEis_degeneracyTransferZero_heckeOperatorHom_comm
-- name    : HeckeEis.degeneracyTransferZero_heckeOperatorHom_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/75e958c8-1346-5ede-ab3a-15ffd1c37e56
-- title:
--   Hecke equivariance of the twisted degeneracy transfer
-- statement:
--   Fix natural numbers $N$ and $q'$, both assumed nonzero, with $q'$ prime and $q' \nmid N$. The assertion is universally quantified over a further natural number $\ell$, again assumed nonzero, which is prime and does not divide $N q'$, and over an arbitrary additive homomorphism $x \colon \mathrm{Additive}(\Gamma_0(Nq')) \to \mathbb{Z}$, i.e. an integral character of the group $\Gamma_0(Nq')$ written additively. Here `heckeOperatorHom M ℓ ℤ` is the $\mathbb{Z}$-linear endomorphism of integral characters of $\Gamma_0(M)$ obtained as the composite of pullback along the homomorphism `heckeConj M ℓ` from `heckeUpper M ℓ` (the subgroup of $\Gamma_0(M)$ consisting of the elements lying in `heckeUpperSL ℓ`) to $\Gamma_0(M)$, given by conjugation by the Hecke matrix at $\ell$, followed by the group-theoretic transfer (corestriction) from `heckeUpper M ℓ` back to $\Gamma_0(M)$, the latter being the sum over the coset space of the transfer cocycle. The conclusion is that the map `degeneracyTransfer₀ N q' ℤ hq' hq'N`, from integral characters of $\Gamma_0(Nq')$ to integral characters of $\Gamma_0(N)$, intertwines these operators: applying `heckeOperatorHom (N * q') ℓ ℤ` to $x$ and then the transfer gives the same result as applying the transfer to $x$ and then `heckeOperatorHom N ℓ ℤ`.
--
--   This is the integral character-group form of the classical statement that degeneracy (trace) maps between levels $Nq'$ and $N$ commute with the Hecke operators at primes away from the level, here for the Atkin–Lehner-twisted degeneracy map `degeneracyTransfer₀`. It is used in the level-raising part of the argument, in [`LevelRaising.qNewSupport_comap_of_isNormalizedEigenform_oddPrime`](thm.html#LevelRaising.qNewSupport_comap_of_isNormalizedEigenform_oddPrime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_degeneracyTransferZero_heckeOperatorHom_comm.lean

import Definitions.Def_HeckeEis_DegeneracyTransfers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CongruenceSubgroup HeckeEis

theorem HeckeEis.degeneracyTransferZero_heckeOperatorHom_comm (N q' : ℕ) [NeZero N] [NeZero q']
    (hq' : q'.Prime) (hq'N : ¬ q' ∣ N) :
    ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q' →
      ∀ x : Additive (Gamma0 (N * q')) →+ ℤ,
        degeneracyTransfer₀ N q' ℤ hq' hq'N (heckeOperatorHom (N * q') ℓ ℤ x) =
          heckeOperatorHom N ℓ ℤ (degeneracyTransfer₀ N q' ℤ hq' hq'N x) := by sorry
