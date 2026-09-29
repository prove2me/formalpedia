-- Prove2me | Theorems.Thm_FreyPackage_frey_wild_inertia_at_two_trivial
-- name    : FreyPackage.frey_wild_inertia_at_two_trivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/903a7643-e5e4-5c8c-809b-2d7b8b332ac5
-- title:
--   Wild inertia at 2 fixes the p-torsion of a Frey curve
-- statement:
--   Let $P$ be a Frey package: nonzero integers $a,b,c$, a prime exponent $p\ge 5$ with $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$ and $b\equiv 0\pmod 2$, and let $P.\mathrm{freyCurve}$ be the associated Weierstrass curve over $\mathbb{Q}$ with $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$. The assertion is: for every valuation subring $A$ of $\overline{\mathbb{Q}}=$ `AlgebraicClosure ℚ` lying over the prime $2$, in the sense that the image of $2$ in $\overline{\mathbb{Q}}$ belongs to the set of nonunits of $A$ (its maximal ideal), and for every $\sigma$ in the inertia subgroup of $A$ over $\mathbb{Q}$ viewed inside $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$, i.e. in the image of the inertia subgroup of $A$ under the inclusion of the decomposition subgroup, which satisfies the wildness condition that $\sigma(z)z^{-1}-1$ lies in the nonunits of $A$ for every $z\neq 0$ in $\overline{\mathbb{Q}}$, the automorphism $\sigma$ fixes every element $x$ of the $p$-torsion submodule $\{x : p\,x = 0\}$ of the group of points of the base change of $P.\mathrm{freyCurve}$ to $\overline{\mathbb{Q}}$: one has $\sigma\cdot x = x$.
--
--   This is the wild half of the classical statement that inertia at $2$ acts unipotently, indeed through a group of order dividing the odd prime $p$, on the $p$-torsion of the Frey curve, which has multiplicative reduction at $2$; the tame part is supplied separately. It is used by [`FreyPackage.frey_inertia_at_two_trivial_on_stable_submodule`](thm.html#FreyPackage.frey_inertia_at_two_trivial_on_stable_submodule), on the way to the assertion that inertia at $2$ acts trivially on a Galois-stable line in $E[p]$ and on its quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_frey_wild_inertia_at_two_trivial.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem FreyPackage.frey_wild_inertia_at_two_trivial (P : FreyPackage) : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 2 → ∀ σ ∈ A.inertiaSubgroupIn ℚ, (∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ A.nonunits) → ∀ x : Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p, σ • x = x := by sorry
