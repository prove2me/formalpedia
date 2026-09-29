-- Prove2me | Theorems.Thm_FreyPackage_eigenformResidualAttachmentAtFamily
-- name    : FreyPackage.eigenformResidualAttachmentAtFamily
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/0050105f-23b7-5bae-8a09-414707f53844
-- title:
--   Eichler–Shimura residual attachment at every level
-- statement:
--   Let $P$ be a [`FreyPackage`](def/FLTPrelim_FreyPackage.html#L17), i.e. nonzero integers $a,b,c$ and a prime $p\ge 5$ with $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$ and $b\equiv 0\pmod 2$. The theorem asserts that for every natural number $M>0$ the project predicate `P.EigenformResidualAttachmentAt M` holds, which unfolds as follows: for every weight-$2$ cusp form $g$ for $\Gamma_0(M)$ satisfying the project's predicate `IsNormalizedEigenform`, and every maximal ideal $\mathfrak m$ of the integral closure of $\mathbb Z$ in $\mathbb C$ (the algebraic integers) with $p\in\mathfrak m$, there exist a field $K$ carrying an algebra structure over $\mathbb Z/p$ (so of characteristic $p$), a $K$-vector space $V$, a representation $\rho$ of the group $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, realised as the $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`, by $K$-linear endomorphisms of $V$, a ring homomorphism $\psi$ from the algebraic integers to $K$, and a number field $F$, Galois over $\mathbb Q$ and embedded in $\overline{\mathbb Q}$ compatibly with $\mathbb Q$, such that: (i) $\mathfrak m\subseteq\ker\psi$; (ii) $\dim_K V=2$; (iii) the kernel of the restriction homomorphism $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)\to\mathrm{Gal}(F/\mathbb Q)$ is contained in the intersection of $\ker\rho$ with the kernel of the project's mod-$p$ Galois representation `galoisRepModuleEnd` attached to the Frey curve `P.freyCurve` at $p$, so that both representations factor through $\mathrm{Gal}(F/\mathbb Q)$; (iv) for every prime $\ell$ with $\ell\nmid M$ and $\ell\ne p$, every valuation subring $A$ of $\overline{\mathbb Q}$ with `A.LiesOverPrime ℓ` and every $\tau$ with `A.IsFrobeniusAt τ ℓ`, there is an algebraic integer $a$ whose image in $\mathbb C$ is the $\ell$-th $q$-expansion coefficient `qCoeff g ℓ` and with $\operatorname{tr}\rho(\tau)=\psi(a)$; and (v) under the same quantification, $\det\rho(\tau)=\ell$ in $K$. The notions `IsNormalizedEigenform`, `qCoeff`, `galoisRepModuleEnd`, `LiesOverPrime` and `IsFrobeniusAt` are the project's own; no continuity, irreducibility, or behaviour at $\ell\mid M$ or at $p$ is asserted, and $K$ is not required to be finite or related to the Hecke field beyond the existence of $\psi$.
--
--   This is the residual (mod $\mathfrak m$) form of the Eichler–Shimura construction of the two-dimensional Galois representation attached to a weight-$2$ eigenform on $\Gamma_0(M)$, as in the attachment clause of Darmon–Diamond–Taylor's Theorem 3.1, stated uniformly in the level $M$. Compared with the textbook statement it is deliberately weaker in shape: the coefficient field is only some characteristic-$p$ field receiving the algebraic integers modulo $\mathfrak m$, the representation is an abstract $K$-linear action of the absolute Galois group with no continuity or irreducibility hypothesis, and the only arithmetic content is the trace and determinant formulas at Frobenius elements for primes $\ell\nmid Mp$, together with the clause forcing $\rho$ and the mod-$p$ representation of the Frey curve to factor through one common finite Galois extension $F/\mathbb Q$ (which is what allows the two to be compared). It is used in the level-lowering step [`FreyPackage.level_lowering_odd_prime_of_conductorLevel`](thm.html#FreyPackage.level_lowering_odd_prime_of_conductorLevel), to transport congruences between levels, and in [`FreyPackage.routeAReversePinBadOnlySeam`](thm.html#FreyPackage.routeAReversePinBadOnlySeam).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_eigenformResidualAttachmentAtFamily.lean

import Mathlib
import Definitions.Def_FreyPackage_EigenformResidualAttachment

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FreyPackage.eigenformResidualAttachmentAtFamily (P : FreyPackage) :
    ∀ M : ℕ, 0 < M → P.EigenformResidualAttachmentAt M := by sorry
