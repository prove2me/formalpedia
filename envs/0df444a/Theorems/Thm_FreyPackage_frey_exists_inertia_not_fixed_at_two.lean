-- Prove2me | Theorems.Thm_FreyPackage_frey_exists_inertia_not_fixed_at_two
-- name    : FreyPackage.frey_exists_inertia_not_fixed_at_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/7e3e6c78-538d-5b54-a153-a7a1a3009c78
-- title:
--   The Frey curve's p-torsion is ramified at 2
-- statement:
--   Let $P$ be a Frey package, that is, nonzero integers $a,b,c$ and a prime $p\ge 5$ with $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$ and $b\equiv 0\pmod 2$, and let $P.\mathtt{freyCurveInt}$ be the associated integral Weierstrass curve with $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $2$, in the sense that $2$ is a nonunit of $A$. Then there is an element $\tau$ of the inertia subgroup of $A$ in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ — the image, under the inclusion of the decomposition subgroup of $A$ into $\overline{\mathbb Q}\simeq_{\mathbb Q}\overline{\mathbb Q}$, of the inertia subgroup of $A$ over $\mathbb Q$ — and a point $x$ of the $p$-torsion submodule $\{x \mid p\cdot x = 0\}$ of the group of $\overline{\mathbb Q}$-points of the base change to $\mathbb Q$ of that curve, such that $\tau\cdot x \ne x$. In other words, inertia at $2$ does not act trivially on the $p$-torsion of the Frey curve.
--
--   This is the "très ramifié" property of the Frey curve at $2$ in Serre's sense: the mod $p$ representation attached to the Frey curve is ramified at $2$, because the curve has multiplicative reduction there with $p \nmid v_2(\Delta)$. It is used, together with the unramifiedness statements at the odd primes dividing $abc$, in the level-lowering step of the Fermat deduction, and is cited by [`FreyPackage.frey_no_cofixed_of_a_mod_eight`](thm.html#FreyPackage.frey_no_cofixed_of_a_mod_eight).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_frey_exists_inertia_not_fixed_at_two.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem FreyPackage.frey_exists_inertia_not_fixed_at_two (P : FreyPackage)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime 2) :
    ∃ τ ∈ A.inertiaSubgroupIn ℚ,
      ∃ x : Submodule.torsionBy ℤ
          ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point P.p,
        τ • x ≠ x := by sorry
