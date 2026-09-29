-- Prove2me | Theorems.Thm_HeckeEis_heckeOperatorHom_smul
-- name    : HeckeEis.heckeOperatorHom_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/d5fe5622-6e07-5274-99cb-cea9d3da0a63
-- title:
--   Scalar equivariance of the Hecke operator on characters
-- statement:
--   Let $N$ and $\ell$ be natural numbers with $\ell \neq 0$, let $A$ be an additive commutative group, and let $R$ be a monoid acting on $A$ by a distributive multiplicative action. Let $r \in R$ and let $\varphi \colon \mathrm{Additive}(\Gamma_0(N)) \to A$ be an additive homomorphism, where $\Gamma_0(N)$ is the congruence subgroup of $\mathrm{SL}_2(\mathbb{Z})$ written additively via `Additive`. The assertion is that the operator [`HeckeEis.heckeOperatorHom N ℓ A`](def/Gamma0HeckeOperatorHom.html#L285) commutes with the pointwise action of $r$ on such homomorphisms: applying it to $r \bullet \varphi$ gives $r \bullet$ (its value on $\varphi$). Here [`HeckeEis.heckeOperatorHom N ℓ A`](def/Gamma0HeckeOperatorHom.html#L285) is the additive endomorphism of $\mathrm{Hom}(\mathrm{Additive}(\Gamma_0(N)), A)$ obtained by first restricting along the monoid homomorphism [`HeckeEis.heckeConj N ℓ`](def/Gamma0HeckeOperatorHom.html#L172) from the subgroup [`HeckeEis.heckeUpper N ℓ`](def/Gamma0HeckeOperatorHom.html#L128) $= (\mathrm{heckeUpperSL}\ \ell).\mathrm{subgroupOf}\ \Gamma_0(N)$ into $\Gamma_0(N)$ (given on matrices by `heckeConjMat ℓ`), and then applying corestriction [`HeckeEis.coresHom`](def/Gamma0HeckeOperatorHom.html#L238), which sends a homomorphism $\psi$ on the subgroup to $g \mapsto \sum_{q} \psi(\mathrm{transferAux}\ g\ q)$, the sum being over the (finite) coset space $\Gamma_0(N)/\mathrm{heckeUpper}(N,\ell)$.
--
--   This is the $R$-equivariance (projection-type) property of the transfer-based Hecke operator on degree-one characters of $\Gamma_0(N)$: when $R$ is a ring and $A$ an $R$-module, it says that the operator is an $R$-linear endomorphism of $\mathrm{Hom}(\Gamma_0(N), A)$. It is used in [`CohCarrier.exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms`](thm.html#CohCarrier.exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms), where the Hecke operators must be realised inside the endomorphism ring of a module of parabolic homomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_heckeOperatorHom_smul.lean

import Definitions.Def_Gamma0HeckeOperatorHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup Subgroup

theorem HeckeEis.heckeOperatorHom_smul (N ℓ : ℕ) [NeZero ℓ] {A : Type*} [AddCommGroup A]
    {R : Type*} [Monoid R] [DistribMulAction R A] (r : R)
    (φ : Additive ↥(Gamma0 N) →+ A) :
    HeckeEis.heckeOperatorHom N ℓ A (r • φ) =
      r • HeckeEis.heckeOperatorHom N ℓ A φ := by sorry
