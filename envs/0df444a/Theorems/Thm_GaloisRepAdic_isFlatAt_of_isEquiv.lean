-- Prove2me | Theorems.Thm_GaloisRepAdic_isFlatAt_of_isEquiv
-- name    : GaloisRepAdic.isFlatAt_of_isEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/098a5584-b8eb-5c4a-ae3a-3fcab5c214d5
-- title:
--   Flatness at p is invariant under equivalence
-- statement:
--   Let $A$ be a commutative local ring and let $\rho_1,\rho_2$ be objects of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16), that is, each consists of a finite free $A$-module $V$ of rank $2$ together with a monoid homomorphism $\rho$ from $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\mathrm{End}_A(V)$ satisfying the adic continuity condition that for every $n$ there is a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ with $\rho(\sigma)v-v\in\mathfrak m_A^n\cdot V$ for all $v\in V$ and all $\sigma$ fixing $L$ pointwise. Assume `IsEquiv` holds, i.e. there exists an $A$-linear isomorphism $\rho_1.V\to\rho_2.V$ intertwining the two actions of every $\sigma$. Assume further that $\rho_1$ is flat at a natural number $p$ in the sense of `IsFlatAt`: the residue field of $A$ is finite, and for every ideal $I$ of $A$ with $A/I$ finite there is a commutative ring $H$ carrying a cocommutative Hopf algebra structure over the subring $\mathbb Z_{(p)}\subset\mathbb Q$ of rationals whose denominator is coprime to $p$, module-finite and flat over that subring, together with a bijection $e$ from the convolution monoid of $\mathbb Z_{(p)}$-algebra maps $H\to\overline{\mathbb Q}$ onto $\rho_1.V/(I\cdot \rho_1.V)$ which carries convolution to addition and is equivariant in the sense that if $g=\sigma\circ f$ pointwise on $H$ then $e(g)$ is the induced action of $\sigma$ on the quotient applied to $e(f)$. The conclusion is that $\rho_2$ is flat at $p$ in the same sense.
--
--   This is the elementary half of the assertion that the flat local condition at $p$ is a deformation condition: invariance of the condition under equivalence of the representation (stability under base change and subquotients is not asserted here). It is used wherever flat or minimally flat local conditions are attached to rank-two adic Galois representations, for instance in the comparison of flatness with ordinarity for Hecke-algebra valued representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isFlatAt_of_isEquiv.lean

import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.isFlatAt_of_isEquiv
    {A : Type} [CommRing A] [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ}
    (h : ρ₁.IsFlatAt p) : ρ₂.IsFlatAt p := by sorry
