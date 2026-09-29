-- Prove2me | Theorems.Thm_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt
-- name    : GaloisRepAdic.isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/2957e862-bd88-5e38-b38d-782a3bca33f8
-- title:
--   Unramified residual representations are finite flat at p
-- statement:
--   Let $k$ be a finite field and let $\rho$ be a residual Galois representation over $k$: a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, taken as the group of $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`, to $\mathrm{End}_k(V)$ which factors through a finite level, i.e. there is an intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$ with $[L:\mathbb Q]$ finite such that every $\sigma$ fixing $L$ pointwise acts as the identity on $V$. Let $p$ be a prime. Viewing $\rho$ as an adic Galois representation over the local ring $k$ via [`GaloisRepAdic.ofResidualGaloisRep`](def/GaloisRep_Adic.html#L196) (same $V$ and same homomorphism, adic continuity coming from the finite level), assume it is unramified at $p$: for every valuation subring $P$ of $\overline{\mathbb Q}$ with $p$ a non-unit of $P$, every element of the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $P$ over $\mathbb Q$ acts as the identity on $V$. The conclusion is that this representation is flat at $p$ in the sense of [`GaloisRepAdic.IsFlatAt`](def/GaloisRep_Flat.html#L29): the residue field of $k$ is finite, and for every ideal $I$ of $k$ with $k/I$ finite there exist a commutative ring $H$ carrying a Hopf algebra structure over the subring $\mathbb Z_{(p)} \subset \mathbb Q$ of rationals whose denominator is coprime to $p$, such that $H$ is finite and flat as a $\mathbb Z_{(p)}$-module and cocommutative as a coalgebra, together with a bijection $e$ from the set of $\mathbb Z_{(p)}$-algebra homomorphisms $H \to \overline{\mathbb Q}$, equipped with its convolution multiplication, onto $V/(I\cdot V)$ which sends convolution products to sums, $e(f\cdot g) = e(f) + e(g)$, and is Galois-equivariant: whenever $g(h) = \sigma(f(h))$ for all $h \in H$, one has $e(g) = \overline{\rho}(\sigma)\,e(f)$ for the action induced by $\sigma$ on $V/(I\cdot V)$.
--
--   This is the statement that a finite Galois module which is unramified above $p$ arises from a finite flat (indeed étale) commutative group scheme over $\mathbb Z_{(p)}$, so that the unramified condition implies the flat condition at $p$ in the deformation-theoretic sense used here. It is cited by [`CuspForm.TWLevel.HeckeRing.isStrictOrdinaryAt_of_dvd_level_of_not_isFlatAt`](thm.html#CuspForm.TWLevel.HeckeRing.isStrictOrdinaryAt_of_dvd_level_of_not_isFlatAt), where failure of flatness at $p$ is converted into ordinarity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt.lean

import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt
    {k : Type} [Field k] [Finite k] (ρ : ResidualGaloisRep k) {p : ℕ} (hp : p.Prime)
    (h : (GaloisRepAdic.ofResidualGaloisRep ρ).IsUnramifiedAt p) :
    (GaloisRepAdic.ofResidualGaloisRep ρ).IsFlatAt p := by sorry
