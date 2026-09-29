-- Prove2me | Theorems.Thm_HeckeEis_heckeOperatorHom_commute
-- name    : HeckeEis.heckeOperatorHom_commute
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/7d98823d-1d6c-5b4b-9b63-1ec5500df185
-- title:
--   Commutativity of the Hecke operators on Hom(Γ₀(N),A)
-- statement:
--   Fix a level $N \in \mathbb{N}$, an additively written abelian group $A$, two primes $\ell_1, \ell_2$ and an additive homomorphism $\varphi : \mathrm{Additive}(\Gamma_0(N)) \to A$, i.e. a homomorphism from $\Gamma_0(N)$ into $A$. For a nonzero natural number $\ell$ the operator `heckeOperatorHom N ℓ A` on the group of such homomorphisms is the composite of two maps: first `pullbackHom (heckeConj N ℓ)`, precomposition with the group homomorphism `heckeConj N ℓ` from the subgroup `heckeUpper N ℓ` of $\Gamma_0(N)$ — the elements of $\Gamma_0(N)$ lying in the subgroup `heckeUpperSL ℓ` of $SL_2(\mathbb{Z})$ — to $\Gamma_0(N)$, given on matrix entries by `heckeConjMat ℓ` (conjugation by the $\ell$-dilation, which lands back in $\Gamma_0(N)$ on this subgroup); and then `coresHom (heckeUpper N ℓ)`, the corestriction (transfer) map sending a homomorphism $\psi$ on `heckeUpper N ℓ` to $g \mapsto \sum_{q \in \Gamma_0(N)/\mathrm{heckeUpper}} \psi(\mathrm{transferAux}\ g\ q)$, the sum over the finitely many cosets of the transfer cocycle. The assertion is that applying `heckeOperatorHom N ℓ₁ A` after `heckeOperatorHom N ℓ₂ A` to $\varphi$ gives the same homomorphism as applying them in the opposite order; the nonvanishing of $\ell_1,\ell_2$ comes from their primality. No coprimality of $\ell_1$ or $\ell_2$ with $N$ is assumed.
--
--   This is the commutativity of the Hecke operators $T_\ell$ (including the case $\ell \mid N$, classically written $U_\ell$) in the group-cohomological incarnation as corestriction–conjugation operators on $\mathrm{Hom}(\Gamma_0(N), A)$. It is used in the level-raising part of the argument, in the analysis of the $q$-new support attached to a normalised eigenform at an odd prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_heckeOperatorHom_commute.lean

import Definitions.Def_Gamma0HeckeOperatorHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup HeckeEis

theorem HeckeEis.heckeOperatorHom_commute (N : ℕ) (A : Type*) [AddCommGroup A]
    (ℓ₁ ℓ₂ : Nat.Primes) (φ : Additive (Gamma0 N) →+ A) :
    haveI : NeZero (ℓ₁ : ℕ) := ⟨ℓ₁.2.ne_zero⟩
    haveI : NeZero (ℓ₂ : ℕ) := ⟨ℓ₂.2.ne_zero⟩
    heckeOperatorHom N ℓ₁ A (heckeOperatorHom N ℓ₂ A φ) =
      heckeOperatorHom N ℓ₂ A (heckeOperatorHom N ℓ₁ A φ) := by sorry
