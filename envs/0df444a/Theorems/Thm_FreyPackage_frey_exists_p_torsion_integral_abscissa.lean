-- Prove2me | Theorems.Thm_FreyPackage_frey_exists_p_torsion_integral_abscissa
-- name    : FreyPackage.frey_exists_p_torsion_integral_abscissa
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/d4441bb8-aa50-500f-a561-eb9d8de5658f
-- title:
--   Stable line yields p-torsion point with A-integral abscissa
-- statement:
--   Let $P$ be a Frey package: nonzero integers $a,b,c$ and a prime $p\ge 5$ with $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$ and $b\equiv 0\pmod 2$; let $E=$ `P.freyCurve` be the associated Weierstrass curve over $\mathbb{Q}$ with $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$. Assume $p\nmid abc$ in $\mathbb{Z}$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}=$ `AlgebraicClosure ℚ` lying over $p$ in the sense that $p$, viewed in $\overline{\mathbb{Q}}$, belongs to the nonunits of $A$. Let $N$ be a $\mathbb{Z}/p$-submodule of the $p$-torsion subgroup $E(\overline{\mathbb{Q}})[p]$ (the $\mathbb{Z}$-torsion by $p$ of the point group of $E$ base-changed to $\overline{\mathbb{Q}}$) which is Galois stable, i.e. $\sigma\cdot x\in N$ for every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$ and every $x\in N$, and suppose $N\neq 0$ and $N\neq E(\overline{\mathbb{Q}})[p]$. Then there exist an element $t$ of $E(\overline{\mathbb{Q}})[p]$, coordinates $x,y\in\overline{\mathbb{Q}}$ and a proof that $(x,y)$ is a nonsingular point of the affine model of $E$ over $\overline{\mathbb{Q}}$, such that $t$, as a point of $E(\overline{\mathbb{Q}})$, is the affine point $(x,y)$, and $x\in A$. In particular $t$ is not the point at infinity; the conclusion does not assert that $t$ lies in $N$.
--
--   This is the statement that a reducible mod $p$ representation rules out supersingular reduction at $p$: not all of $E[p]$ can lie in the kernel of reduction at a place above $p$, so some nonzero $p$-torsion point has abscissa integral at that place. It feeds the local analysis at $p$ for the Frey curve with good reduction there, being used by [`FreyPackage.frey_inertia_at_p_filtration_of_not_dvd_abc`](thm.html#FreyPackage.frey_inertia_at_p_filtration_of_not_dvd_abc).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_frey_exists_p_torsion_integral_abscissa.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem FreyPackage.frey_exists_p_torsion_integral_abscissa (P : FreyPackage) (hgood : ¬ (P.p : ℤ) ∣ P.a * P.b * P.c) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime P.p) (N : Submodule (ZMod P.p) (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p)) (hN : IsGaloisStable (K := AlgebraicClosure ℚ) ℚ N) (hbot : N ≠ ⊥) (htop : N ≠ ⊤) : ∃ (t : Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p) (x y : AlgebraicClosure ℚ) (h : (P.freyCurve⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y), (t : (P.freyCurve⁄(AlgebraicClosure ℚ)).Point) = Point.some x y h ∧ x ∈ A := by sorry
