-- Prove2me | Theorems.Thm_FreyPackage_freyGaloisRep_isUnramifiedAt
-- name    : FreyPackage.freyGaloisRep_isUnramifiedAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/3c8ae7da-5d8c-5c22-9bde-6466d6175b50
-- title:
--   Frey p-torsion is unramified outside {2,p}
-- statement:
--   Let $P$ be a Frey package: nonzero integers $a,b,c$ and a prime $p\ge 5$ with $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3\pmod 4$ and $b\equiv 0\pmod 2$, and let $P.freyCurve$ be the associated Weierstrass curve over $\mathbb{Q}$ with $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$. Let $q$ be a natural number that is prime, with $q\ne 2$ and $q\ne p$. The conclusion is the project predicate [`FreyPackage.GaloisRepUnramifiedAt`](def/FLTPrelim_Ramification.html#L46) for $P$ at $q$, which unfolds to the following assertion about the $p$-torsion of the Frey curve over a fixed algebraic closure $\overline{\mathbb{Q}}$ = `AlgebraicClosure ℚ`: for every valuation subring $A$ of $\overline{\mathbb{Q}}$ such that the image of $q$ lies in the nonunits of $A$ (the project's `LiesOverPrime`, i.e. $A$ is a valuation ring of $\overline{\mathbb{Q}}$ at which $q$ is not invertible), for every automorphism $\sigma\in\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ lying in the image in the full Galois group of the inertia subgroup of $A$ over $\mathbb{Q}$ (the project's `inertiaSubgroupIn`, the inertia subgroup of the decomposition subgroup pushed forward along its inclusion), and for every element $x$ of `Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p` — the $p$-torsion submodule of the group of affine points of the Frey curve over $\overline{\mathbb{Q}}$ — one has $\sigma\bullet x=x$, where the action is induced by functoriality of points along $\sigma$. Thus inertia at every place above $q$ fixes the full $p$-torsion pointwise; no hypothesis relating $q$ to $abc$ is imposed.
--
--   This is the ramification statement for the mod-$p$ representation of the Frey curve used by Serre and Ribet: $E_P[p]$ is unramified at every odd prime $q\ne p$, because $E_P$ has either good or multiplicative reduction at $q$ and, in the multiplicative case, $p$ divides $v_q(\Delta)$ since $\Delta = 2^{-8}(abc)^{2p}$. In contrast with the textbook formulation in terms of a representation $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})\to\mathrm{GL}_2(\mathbb{F}_p)$ being unramified, the formal statement is phrased as pointwise triviality of the action of inertia subgroups attached to valuation subrings of $\overline{\mathbb{Q}}$ on the $p$-torsion module of the affine point group. It feeds the level-lowering steps ([`FreyPackage.level_lowering_to_two_of_conductorLevel`](thm.html#FreyPackage.level_lowering_to_two_of_conductorLevel)) and the analysis of Galois-stable submodules of $E_P[p]$ ([`FreyPackage.frey_stable_submodule_fixed_or_cofixed`](thm.html#FreyPackage.frey_stable_submodule_fixed_or_cofixed)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_freyGaloisRep_isUnramifiedAt.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open CuspForm ModularFormClass UpperHalfPlane

theorem FreyPackage.freyGaloisRep_isUnramifiedAt (P : FreyPackage) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ P.p) : P.GaloisRepUnramifiedAt q := by sorry
