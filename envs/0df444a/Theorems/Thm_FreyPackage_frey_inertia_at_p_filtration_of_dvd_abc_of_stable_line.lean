-- Prove2me | Theorems.Thm_FreyPackage_frey_inertia_at_p_filtration_of_dvd_abc_of_stable_line
-- name    : FreyPackage.frey_inertia_at_p_filtration_of_dvd_abc_of_stable_line
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/44e88cdb-f26a-5c53-af22-fcb926691dc5
-- title:
--   Inertia at p∣ abc acts trivially modulo a proper subspace
-- statement:
--   Let $P$ be a Frey package: nonzero integers $a,b,c$ and a prime $p\ge 5$ with $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$ and $b\equiv 0\pmod 2$, and let $E=$ `P.freyCurve` be the associated Weierstrass curve over $\mathbb{Q}$ with $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$. Assume $p \mid abc$ in $\mathbb{Z}$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$, in the sense that the image of $p$ in $\overline{\mathbb{Q}}$ is a nonunit of $A$. Let $N$ be a $\mathbb{Z}/p$-submodule of the $p$-torsion $E[p]=$ `Submodule.torsionBy ℤ` of the group of points of $E$ over $\overline{\mathbb{Q}}$, assumed Galois stable in the sense that $\sigma\cdot x\in N$ for every $\sigma\in\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ and every $x\in N$, and assume $N\neq 0$ and $N\neq E[p]$. Then there exists a $\mathbb{Z}/p$-submodule $M$ of $E[p]$ with $M\neq E[p]$ such that $\sigma\cdot y-y\in M$ for every $\sigma$ in the image in $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of the decomposition subgroup of $A$ over $\mathbb{Q}$ and every $y\in E[p]$.
--
--   This is the multiplicative-reduction local analysis at $p$ for the Frey curve: inertia at a place above $p$ acts trivially on the quotient of $E[p]$ by the Tate line, so that $\bar\rho_{E,p}$ restricted to inertia at $p$ is upper triangular with trivial quotient character. It feeds into [`FreyPackage.frey_inertia_at_p_trivial_on_submodule_or_quotient_at`](thm.html#FreyPackage.frey_inertia_at_p_trivial_on_submodule_or_quotient_at), the step showing that the sub- or quotient character attached to a Galois-stable line is unramified at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_frey_inertia_at_p_filtration_of_dvd_abc_of_stable_line.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem FreyPackage.frey_inertia_at_p_filtration_of_dvd_abc_of_stable_line (P : FreyPackage) (hbad : (P.p : ℤ) ∣ P.a * P.b * P.c) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime P.p) (N : Submodule (ZMod P.p) (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p)) (hN : IsGaloisStable (K := AlgebraicClosure ℚ) ℚ N) (hbot : N ≠ ⊥) (htop : N ≠ ⊤) : ∃ M : Submodule (ZMod P.p) (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p), M ≠ ⊤ ∧ ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ y : Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p, σ • y - y ∈ M := by sorry
