-- Prove2me | Theorems.Thm_GaloisRepAdic_isFlatAt_of_jointly_injective
-- name    : GaloisRepAdic.isFlatAt_of_jointly_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/e461adbf-1c90-56b2-9905-c938c493b20c
-- title:
--   Flatness at p descends along jointly injective local maps
-- statement:
--   Let $P$ be a commutative local ring and let $A$, $B$ be commutative local Artinian rings. Let $\pi_A\colon P\to A$ and $\pi_B\colon P\to B$ be ring homomorphisms, each local (non-units go to non-units), and assume the pair is jointly injective: if $\pi_A(x)=0$ and $\pi_B(x)=0$ then $x=0$. Let $\rho$ be a [`GaloisRepAdic`](def/GaloisRep_Adic.html#L16) over $P$, that is, a free finite $P$-module $V$ of rank $2$ together with a multiplicative map $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\mathrm{End}_P V$ such that for every $n$ some finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ has the property that elements fixing $L$ act trivially on $V$ modulo $\mathfrak m_P^n V$. Let $p$ be a natural number, and suppose that both base changes $A\otimes_P V$ and $B\otimes_P V$, with the induced Galois actions, satisfy `IsFlatAt p`: their residue fields are finite and, for every ideal $I$ of the coefficient ring with finite quotient, there is a commutative ring $H$ carrying a cocommutative Hopf algebra structure over the subring of $\mathbb Q$ of rationals whose denominator is coprime to $p$, module-finite and flat over that subring, together with a bijection from the set of its algebra maps to $\overline{\mathbb Q}$ (with the convolution group structure) onto the level quotient $V'/I V'$ carrying convolution to addition and commuting with the Galois actions. The conclusion is that $\rho$ itself satisfies `IsFlatAt p`.
--
--   This is the statement that the flatness condition at $p$ on a two-dimensional Galois representation is reflected by a jointly injective pair of local maps to Artinian local rings; taking $\pi_A=\pi_B$ injective gives reflection along a single injection. It is the flat ingredient of the sub-object and fibre-product axioms for Mazur-style deformation conditions, and is used by [`GaloisRepAdic.flatCondition_of_jointly_injective`](thm.html#GaloisRepAdic.flatCondition_of_jointly_injective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isFlatAt_of_jointly_injective.lean

import Mathlib.RingTheory.Artinian.Ring
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.isFlatAt_of_jointly_injective {P A B : Type} [CommRing P]
    [IsLocalRing P] [CommRing A] [IsLocalRing A] [IsArtinianRing A] [CommRing B] [IsLocalRing B]
    [IsArtinianRing B]
    (πA : P →+* A) (hπA : IsLocalHom πA) (πB : P →+* B) (hπB : IsLocalHom πB)
    (hinj : ∀ x, πA x = 0 → πB x = 0 → x = 0) (ρ : GaloisRepAdic P) {p : ℕ}
    (hA : (ρ.baseChangeAlong πA hπA).IsFlatAt p)
    (hB : (ρ.baseChangeAlong πB hπB).IsFlatAt p) : ρ.IsFlatAt p := by sorry
