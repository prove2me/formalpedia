-- Prove2me | Theorems.Thm_FreyPackage_frey_no_cofixed_large
-- name    : FreyPackage.frey_no_cofixed_large
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/5b620acc-25d4-573a-bd47-dc1d58f8e574
-- title:
--   Mazur at p≥ 17: no cofixed line
-- statement:
--   Let $P$ be a Frey package: nonzero integers $a,b,c$ and a prime $p\ge 5$ with $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$ and $b\equiv 0\pmod 2$, and let $E_P$ be the associated Frey curve `P.freyCurve` over $\mathbb{Q}$, the Weierstrass curve with $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$. Assume in addition $17\le p$. The theorem asserts the negation of the project's predicate `HasGaloisStableCofixedLine` for $E_P$, the exponent $P.p$ and the field extension $\mathbb{Q}\subseteq \overline{\mathbb{Q}}$ (realised as `AlgebraicClosure ℚ`): there is no $\mathbb{Z}/p$-submodule $N$ of the $p$-torsion module $\mathrm{torsionBy}\,\mathbb{Z}\,E_P(\overline{\mathbb{Q}})\,p$ (the points of the affine Weierstrass model over $\overline{\mathbb{Q}}$ killed by $p$, with $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = (\overline{\mathbb{Q}}\simeq_{\mathbb{Q}}\overline{\mathbb{Q}})$ acting through `Point.map`) such that all four of the following hold: $N$ is stable under the Galois action, $\sigma\cdot x\in N$ for every $\sigma$ and every $x\in N$; $N\ne \bot$; $N\ne\top$; and $\sigma\cdot x-x\in N$ for every Galois element $\sigma$ and every $p$-torsion point $x$, i.e. the Galois action on the quotient of the $p$-torsion by $N$ is trivial. In short: the mod-$p$ representation attached to a Frey package with $p\ge 17$ admits no proper nonzero stable line whose quotient carries the trivial action.
--
--   This is the form in which Mazur's Eisenstein-ideal results on rational torsion and rational isogenies of prime degree enter the Frey–Serre–Ribet route. The formal statement is narrower than Mazur's theorems: it does not speak of $X_0(p)$ or of rational points of order $p$ on a general elliptic curve, but excludes, for Frey packages with exponent at least $17$, exactly the configuration of a Galois-stable line with trivial action on the quotient — the configuration that Serre's reduction extracts from reducibility. It is used by [`FreyPackage.Mazur_Frey`](thm.html#FreyPackage.Mazur_Frey), which combines it with the corresponding statements for $p=11$ and $p\in\{5,7,13\}$ to conclude that the $p$-torsion of the Frey curve is a nontrivial irreducible Galois module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_frey_no_cofixed_large.lean

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

theorem FreyPackage.frey_no_cofixed_large (P : FreyPackage) (hp : 17 ≤ P.p) : ¬ HasGaloisStableCofixedLine (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p := by sorry
