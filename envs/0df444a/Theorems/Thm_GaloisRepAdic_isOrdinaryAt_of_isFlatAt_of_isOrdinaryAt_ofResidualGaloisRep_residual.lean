-- Prove2me | Theorems.Thm_GaloisRepAdic_isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual
-- name    : GaloisRepAdic.isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/21d4e4eb-9797-52a4-9b3c-3a5fa52b7dd0
-- title:
--   Flat lifts of ordinary residual representations are ordinary
-- statement:
--   Let $A$ be a commutative Noetherian local ring which is complete with respect to its maximal ideal $\mathfrak m_A$, let $p$ be a prime with $p \neq 2$, and assume $p \in \mathfrak m_A$. Let $\rho$ be an object of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16): a free finite $A$-module $V$ with $\operatorname{rank}_A V = 2$ together with a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\operatorname{End}_A V$ that is adically continuous, in the sense that for every $n$ there is a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ with $\rho(\sigma)v - v \in \mathfrak m_A^n V$ for all $v \in V$ and all $\sigma$ fixing $L$ pointwise. Three hypotheses are imposed. First, `DetIsCyclotomic`: $p \in \mathfrak m_A$, and whenever $\sigma$ acts on the $p^n$-th roots of unity of $\overline{\mathbb Q}$ by $\mu \mapsto \mu^a$ with $a \in \mathbb N$, one has $\det \rho(\sigma) - a \in (p^n)A$. Second, `IsFlatAt p`: the residue field of $A$ is finite, and for every ideal $I$ with $A/I$ finite there exist a commutative ring $H$ carrying a cocommutative Hopf algebra structure over the subring of $\mathbb Q$ of rationals whose denominator is coprime to $p$, finite and flat as a module over that subring, and a bijection $e$ from the set of algebra maps $H \to \overline{\mathbb Q}$ over that subring, with its convolution multiplication, onto $V/IV$, such that $e$ carries convolution products to sums and intertwines the Galois action on algebra maps with the induced action of $\rho$ on $V/IV$. Third, the residual representation: the $2$-dimensional representation of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ on $k \otimes_A V$, $k$ the residue field of $A$, regarded as an adic representation over $k$, is ordinary at $p$. The conclusion is that $\rho$ is ordinary at $p$: for every valuation subring $P$ of $\overline{\mathbb Q}$ with $p$ a non-unit in $P$, there is an $A$-submodule $L \subseteq V$ of the form $A \cdot b_0$ for some basis $(b_0,b_1)$ of $V$, stable under the decomposition subgroup of $P$ over $\mathbb Q$, and such that $\rho(\sigma)v - v \in L$ for every $\sigma$ in the inertia subgroup of $P$ (taken inside the decomposition subgroup) and every $v \in V$.
--
--   This is the passage from finite flatness at $p$ to ordinarity at $p$ for odd $p$, the analogue of the standard consequence of Raynaud's theory of finite flat group schemes over $\mathbb Z_p$ used when the flat and ordinary deformation conditions are compared. It is used in the verification of the ordinarity condition for the Galois representations attached to cusp forms and in the associated local-ring computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem GaloisRepAdic.isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpA : (p : A) ∈ maximalIdeal A)
    (ρ : GaloisRepAdic A) (hdet : ρ.DetIsCyclotomic p) (hflat : ρ.IsFlatAt p)
    (hres : (GaloisRepAdic.ofResidualGaloisRep ρ.residual).IsOrdinaryAt p) :
    ρ.IsOrdinaryAt p := by sorry
