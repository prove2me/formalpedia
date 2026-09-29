-- Prove2me | Theorems.Thm_FreyPackage_frey_inertia_at_p_filtration_of_not_dvd_abc
-- name    : FreyPackage.frey_inertia_at_p_filtration_of_not_dvd_abc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/1929937a-b682-5aca-a3cb-5c587615300b
-- title:
--   Frey curve, p ∤ abc: inertia above p modulo a proper subspace
-- statement:
--   Let $P$ be a Frey package, i.e. nonzero integers $a,b,c$ together with a prime $p \ge 5$ such that $a^p + b^p = c^p$, $\gcd(a,b) = 1$, $a \equiv 3 \pmod 4$ and $b \equiv 0 \pmod 2$, and let $E = P.\mathtt{freyCurve}$ be the associated Weierstrass curve over $\mathbb{Q}$ with $a_1 = 1$, $a_2 = (b^p - 1 - a^p)/4$, $a_3 = 0$, $a_4 = -a^p b^p/16$, $a_6 = 0$. Assume $p \nmid abc$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$, in the sense that the image of $p$ lies in the nonunits of $A$. Let $N$ be a $\mathbb{Z}/p$-submodule of the group $E[p]$ of $p$-torsion points of $E$ over $\overline{\mathbb{Q}}$ which is Galois stable, i.e. $\sigma \cdot x \in N$ for every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$ and every $x \in N$, and assume $N \ne 0$ and $N \ne E[p]$. Then there is a $\mathbb{Z}/p$-submodule $M \subsetneq E[p]$ such that $\sigma \cdot y - y \in M$ for every $\sigma$ in the image in $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup of $A$ inside its decomposition subgroup, and every $y \in E[p]$.
--
--   This is the good-reduction half of the local analysis at $p$ in the proof that the mod $p$ representation attached to a Frey curve has no Galois-stable line: at a place above $p$ the inertia displacements on $E[p]$ all land in a proper subspace, namely the $p$-torsion in the kernel of reduction. It is used by [`FreyPackage.frey_inertia_at_p_trivial_on_submodule_or_quotient_at`](thm.html#FreyPackage.frey_inertia_at_p_trivial_on_submodule_or_quotient_at).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_frey_inertia_at_p_filtration_of_not_dvd_abc.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem FreyPackage.frey_inertia_at_p_filtration_of_not_dvd_abc (P : FreyPackage) (hgood : ¬ (P.p : ℤ) ∣ P.a * P.b * P.c) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime P.p) (N : Submodule (ZMod P.p) (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p)) (hN : IsGaloisStable (K := AlgebraicClosure ℚ) ℚ N) (hbot : N ≠ ⊥) (htop : N ≠ ⊤) : ∃ M : Submodule (ZMod P.p) (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p), M ≠ ⊤ ∧ ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ y : Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p, σ • y - y ∈ M := by sorry
