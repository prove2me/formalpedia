-- Prove2me | Theorems.Thm_FreyPackage_frey_exists_p_torsion_integral_abscissa_of_stable_line
-- name    : FreyPackage.frey_exists_p_torsion_integral_abscissa_of_stable_line
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/f8a9d93b-b48e-57b9-85c9-42c27db6aaa0
-- title:
--   Frey curve with stable line: a p-torsion point with A-integral abscissa
-- statement:
--   Let $P$ be a Frey package, that is, non-zero integers $a,b,c$ and a prime $p\ge 5$ with $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$ and $b\equiv 0\pmod 2$, and let $E=P.\mathrm{freyCurve}$ be the associated Weierstrass curve over $\mathbb{Q}$ with coefficients $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that the image of $p$ in $\overline{\mathbb{Q}}$ is a non-unit of $A$ (so $p \in A$ and $p$ lies in the maximal ideal of $A$). Let $N$ be a $\mathbb{Z}/p$-submodule of the $p$-torsion $E(\overline{\mathbb{Q}})[p]$ (the $\mathbb{Z}$-torsion-by-$p$ submodule of the points of $E$ base changed to $\overline{\mathbb{Q}}$) which is Galois stable, i.e. $\sigma \cdot x \in N$ for every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$ and every $x \in N$, and assume $N \neq 0$ and $N \neq E(\overline{\mathbb{Q}})[p]$. The conclusion asserts the existence of a $p$-torsion point $t$, of coordinates $x,y \in \overline{\mathbb{Q}}$ and of a proof that $(x,y)$ is a non-singular point of the affine model of $E$ over $\overline{\mathbb{Q}}$, such that $t$, viewed as a point of $E$, is the affine point with coordinates $(x,y)$ (in particular $t$ is not the point at infinity) and $x \in A$.
--
--   This is the statement that, for a Frey curve whose mod $p$ representation admits a Galois-stable line, the $p$-torsion is not entirely contained in the kernel of reduction at a place above $p$ — classically, that a reducible mod $p$ representation rules out supersingular reduction at $p$. It feeds the local analysis at $p$: it is used in the construction of the inertia filtration at $p$ when $p \mid abc$, and in the argument excluding large co-fixed subspaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_frey_exists_p_torsion_integral_abscissa_of_stable_line.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem FreyPackage.frey_exists_p_torsion_integral_abscissa_of_stable_line (P : FreyPackage) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime P.p) (N : Submodule (ZMod P.p) (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p)) (hN : IsGaloisStable (K := AlgebraicClosure ℚ) ℚ N) (hbot : N ≠ ⊥) (htop : N ≠ ⊤) : ∃ (t : Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p) (x y : AlgebraicClosure ℚ) (h : (P.freyCurve⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y), (t : (P.freyCurve⁄(AlgebraicClosure ℚ)).Point) = Point.some x y h ∧ x ∈ A := by sorry
