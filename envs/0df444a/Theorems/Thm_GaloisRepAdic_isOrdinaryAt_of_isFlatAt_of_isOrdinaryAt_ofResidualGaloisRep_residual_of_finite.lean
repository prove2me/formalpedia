-- Prove2me | Theorems.Thm_GaloisRepAdic_isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual_of_finite
-- name    : GaloisRepAdic.isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/a2df6f10-bc65-59b0-a793-b9b4965f95d8
-- title:
--   Flat plus ordinary reduction gives ordinary: finite coefficients
-- statement:
--   Let $A$ be a finite commutative local ring, $p$ a prime with $p \neq 2$, and let $\rho$ be a two-dimensional $p$-adic Galois representation over $A$ in the sense of the project: a finite free $A$-module $V$ with $\operatorname{rank}_A V = 2$ together with a monoid homomorphism $\rho$ from $\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\operatorname{End}_A V$ which is adically continuous, i.e. for every $n$ there is a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ such that $(\rho(\sigma)-1)V \subseteq \mathfrak m^n V$ for all $\sigma$ fixing $L$ pointwise. Assume: (i) $\rho$ has cyclotomic determinant at $p$, that is $p \in \mathfrak m_A$ and, whenever $\sigma$ acts on the $p^n$-th roots of unity by $\mu \mapsto \mu^a$, one has $\det \rho(\sigma) \equiv a \pmod{p^n A}$; (ii) $\rho$ is flat at $p$, i.e. the residue field of $A$ is finite and for every ideal $I$ with $A/I$ finite there is a commutative ring $H$, finite and flat as a module over the subring of $\mathbb Q$ of fractions with denominator coprime to $p$ and carrying a cocommutative Hopf algebra structure over it, together with a bijection from the convolution group of $\overline{\mathbb Q}$-points of $H$ onto $V/IV$ that is additive and carries the natural Galois action to the induced action of $\rho$ on $V/IV$; (iii) the residual representation $k \otimes_A V$, $k$ the residue field of $A$, regarded as a representation with coefficients in the field $k$, is ordinary at $p$. Then $\rho$ is ordinary at $p$: for every valuation subring $P$ of $\overline{\mathbb Q}$ with $p$ a non-unit of $P$ there is a submodule $L \subseteq V$ of the form $A \cdot b_0$ for some $A$-basis $(b_0,b_1)$ of $V$ such that $L$ is stable under the decomposition subgroup of $P$ over $\mathbb Q$ and $(\rho(\sigma)-1)V \subseteq L$ for every $\sigma$ in the inertia subgroup of $P$ over $\mathbb Q$.
--
--   This is the finite-coefficient case of the implication that a flat deformation of an ordinary residual representation is itself ordinary (the comparison of the local conditions (fl) and (ord)/(Se) at an odd prime $p$). It is the input to the general local-coefficient statement [`GaloisRepAdic.isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual`](thm.html#GaloisRepAdic.isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual), obtained from it by passage to the finite quotients of $A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual_of_finite.lean

import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual_of_finite
    {A : Type} [CommRing A] [IsLocalRing A] [Finite A] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρ : GaloisRepAdic A) (hdet : ρ.DetIsCyclotomic p) (hflat : ρ.IsFlatAt p)
    (hres : (GaloisRepAdic.ofResidualGaloisRep ρ.residual).IsOrdinaryAt p) :
    ρ.IsOrdinaryAt p := by sorry
