-- Prove2me | Theorems.Thm_FreyPackage_frey_reducible_hasCofixedLine
-- name    : FreyPackage.frey_reducible_hasCofixedLine
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/d4892a02-3a54-5c71-9af9-7485870fd2f7
-- title:
--   Reducible Frey representation yields a Galois-stable cofixed line
-- statement:
--   Let $P$ be a [`FreyPackage`](def/FLTPrelim_FreyPackage.html#L17): non-zero integers $a,b,c$ and a prime $p\ge 5$ with $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$ and $b\equiv 0\pmod 2$; let `P.freyCurve` be the associated Weierstrass curve over $\mathbb Q$ with $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$. The module in question is $M=$ `Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p`, the $p$-torsion of the group of affine points of `P.freyCurve` over a fixed algebraic closure of $\mathbb Q$, regarded as a $\mathbb Z/p$-module, with the group $\mathrm{Gal} = (\mathrm{AlgebraicClosure}\ \mathbb Q) \simeq_{\mathbb Q} (\mathrm{AlgebraicClosure}\ \mathbb Q)$ of $\mathbb Q$-algebra automorphisms acting by transport of coordinates. The hypothesis is the negation of the project's `GaloisRepIsIrreducible ℚ P.freyCurve P.p`, i.e. it is false that ($M$ is nontrivial and every $\mathbb Z/p$-submodule $N\subseteq M$ satisfying $\sigma\cdot x\in N$ for all $\sigma\in\mathrm{Gal}$, $x\in N$, is $\bot$ or $\top$). The conclusion is the project's `HasGaloisStableCofixedLine ℚ P.freyCurve P.p`: there exists a $\mathbb Z/p$-submodule $N\subseteq M$ which is Galois-stable in the above sense, satisfies $N\neq\bot$ and $N\neq\top$, and is such that $\sigma\cdot x-x\in N$ for every $\sigma\in\mathrm{Gal}$ and every $x\in M$ — that is, $\mathrm{Gal}$ acts trivially on $M/N$. Note that neither hypothesis nor conclusion mentions dimensions: "line" here means only a proper non-zero stable submodule, and the Galois group is taken as the abstract automorphism group, with no topology or continuity condition.
--
--   This is Serre's observation that a Galois-stable line in the $p$-torsion of the Frey curve is either pointwise fixed or cofixed, combined with the fact that the Frey curve has no non-trivial $\mathbb Q$-rational $p$-torsion, so that the fixed alternative is impossible. Compared with the textbook formulation, the statement is phrased without bases or characters: reducibility is the existence of a proper non-zero Galois-stable $\mathbb Z/p$-submodule, and being cofixed is expressed by $\sigma\cdot x-x\in N$ for all $\sigma$ and all $x$; the dichotomy between the sub- and quotient characters being trivial or cyclotomic is not part of this statement but is hidden in the cited lemma [`FreyPackage.frey_stable_submodule_fixed_or_cofixed`](thm.html#FreyPackage.frey_stable_submodule_fixed_or_cofixed). It is used in the contrapositive direction by [`FreyPackage.Mazur_Frey`](thm.html#FreyPackage.Mazur_Frey) and [`FreyPackage.Mazur_Frey_of_a_mod_eight`](thm.html#FreyPackage.Mazur_Frey_of_a_mod_eight), which obtain irreducibility of the mod-$p$ representation once the existence of a cofixed line has been excluded.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_frey_reducible_hasCofixedLine.lean

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

theorem FreyPackage.frey_reducible_hasCofixedLine (P : FreyPackage) (hred : ¬ GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p) : HasGaloisStableCofixedLine (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p := by sorry
