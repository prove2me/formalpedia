-- Prove2me | Theorems.Thm_HeckeEis_postcomp_heckeOperatorHom
-- name    : HeckeEis.postcomp_heckeOperatorHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/792c1707-38de-5ddf-9606-32b3e44a1178
-- title:
--   Naturality of `heckeOperatorHom` in the coefficient group
-- statement:
--   Let $N$ and $\ell$ be natural numbers with $\ell \neq 0$, let $A$ and $B$ be additive commutative groups, let $f : A \to_+ B$ be a homomorphism, and let $\varphi : \mathrm{Additive}\,\Gamma_0(N) \to_+ A$ be an $A$-valued additive character of $\Gamma_0(N)$. The operator [`HeckeEis.heckeOperatorHom N ℓ A`](def/Gamma0HeckeOperatorHom.html#L285) is the composite of the pullback along the monoid homomorphism [`HeckeEis.heckeConj N ℓ`](def/Gamma0HeckeOperatorHom.html#L172) from the subgroup `heckeUpper N ℓ` (the preimage in $\Gamma_0(N)$ of `heckeUpperSL ℓ`, i.e. its `subgroupOf`) to $\Gamma_0(N)$, given on elements by the conjugated matrix `heckeConjMat ℓ`, with the corestriction (transfer) `coresHom` of that subgroup, which sends a character $\psi$ of `heckeUpper N ℓ` to $g \mapsto \sum_{q} \psi(\mathrm{transferAux}\, H\, g\, q)$, the sum being over the finite coset space $\Gamma_0(N)/\,$`heckeUpper N ℓ`. The assertion is the equality of additive homomorphisms $\mathrm{Additive}\,\Gamma_0(N) \to_+ B$: postcomposing with $f$ the image of $\varphi$ under the operator with coefficients $A$ equals the image under the operator with coefficients $B$ of the postcomposite $f \circ \varphi$.
--
--   This is the projection (push–pull) formula for the transfer in degree one: the Hecke operator constructed by pullback along the Hecke conjugation followed by corestriction is natural in the coefficient group, so that $A \mapsto \mathrm{Hom}(\Gamma_0(N), A)$ together with the operator forms a functor with a natural endomorphism. It is used wherever the operator must be compared across a change of coefficients, for instance in the reduction arguments on Eisenstein classes and level-raising kernels that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_postcomp_heckeOperatorHom.lean

import Definitions.Def_Gamma0HeckeOperatorHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup Subgroup

theorem HeckeEis.postcomp_heckeOperatorHom (N ℓ : ℕ) [NeZero ℓ] {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] (f : A →+ B) (φ : Additive ↥(Gamma0 N) →+ A) :
    f.comp (HeckeEis.heckeOperatorHom N ℓ A φ) =
      HeckeEis.heckeOperatorHom N ℓ B (f.comp φ) := by sorry
