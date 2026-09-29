-- Prove2me | Theorems.Thm_FreyPackage_frey_no_cofixed_small
-- name    : FreyPackage.frey_no_cofixed_small
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/a67772d0-8850-5cd6-b375-2fd6b08d6b4e
-- title:
--   No Galois-stable cofixed line for p∈{5,7,13}
-- statement:
--   Let $P$ be a Frey package: by the project's definition this consists of nonzero integers $a,b,c$, a prime $p\ge 5$, the relation $a^p+b^p=c^p$, the coprimality $\gcd(a,b)=1$, and the normalisations $a\equiv 3 \pmod 4$ and $b\equiv 0 \pmod 2$. Its Frey curve `P.freyCurve` is the Weierstrass curve over $\mathbb{Q}$ with coefficients $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$. Assume in addition that $p$ equals $5$, $7$ or $13$. The conclusion is that the predicate `HasGaloisStableCofixedLine` fails for the affine Frey curve over $K=\overline{\mathbb{Q}}$ (realised as `AlgebraicClosure ℚ`), relative to the base field $\mathbb{Q}$ and the level $n=p$. Unfolding the project's definition, this says: there is no $\mathbb{Z}/p$-submodule $N$ of the $p$-torsion subgroup $\{x : p\cdot x = 0\}$ of the group of $K$-points of the Frey curve such that (i) $N$ is stable under the natural action of every $\sigma \in K \simeq_{\text{alg}[\mathbb{Q}]} K$ on points, (ii) $N \ne \bot$ and $N \ne \top$, and (iii) $\sigma\cdot x - x \in N$ for every such $\sigma$ and every $p$-torsion point $x$, i.e. the Galois action on the quotient by $N$ is trivial. Note that no condition of being one-dimensional is imposed on $N$ beyond being a proper nonzero submodule; 'line' in the name is suggestive only.
--
--   In the route followed here, irreducibility of the mod-$p$ representation attached to a Frey package is reduced, via Serre's observation, to excluding a Galois-stable proper nonzero submodule on whose quotient Galois acts trivially; that exclusion is classically Mazur's theorem on rational torsion, with the exponents $p\ge 17$ treated by the Eisenstein-ideal argument and the small exponents treated separately. The present statement covers $p\in\{5,7,13\}$, and it is not an argument about elliptic curves at all: since Fermat's Last Theorem is available outright for these exponents, no Frey package with such a $p$ exists and the conclusion holds vacuously. It is used, together with the companion statements for $p=11$ and for $p\ge 17$, in [`FreyPackage.Mazur_Frey`](thm.html#FreyPackage.Mazur_Frey), which asserts `GaloisRepIsIrreducible ℚ P.freyCurve P.p`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_frey_no_cofixed_small.lean

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

theorem FreyPackage.frey_no_cofixed_small (P : FreyPackage) (hp : P.p = 5 ∨ P.p = 7 ∨ P.p = 13) : ¬ HasGaloisStableCofixedLine (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p := by sorry
