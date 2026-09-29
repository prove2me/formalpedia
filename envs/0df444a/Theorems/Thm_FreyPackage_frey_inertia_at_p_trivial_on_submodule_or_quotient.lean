-- Prove2me | Theorems.Thm_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient
-- name    : FreyPackage.frey_inertia_at_p_trivial_on_submodule_or_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/1e030aa8-ca4c-5334-ab90-8122aca8904f
-- title:
--   Inertia at p acts trivially on a stable submodule of Frey E[p] or on its quotient
-- statement:
--   Let $P$ be a Frey package: nonzero integers $a,b,c$ and a prime $p\ge 5$ with $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$ and $b\equiv 0\pmod 2$, and let $E=$ `P.freyCurve` be the associated Weierstrass curve over $\mathbb{Q}$ with $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$. Let $N$ be a $\mathbb{Z}/p$-submodule of the $p$-torsion $E[p]$ of the points of $E$ over $\overline{\mathbb{Q}}=$ `AlgebraicClosure ℚ` (realised as the $\mathbb{Z}$-torsion-by-$p$ submodule of the point group), assumed Galois stable in the sense that $\sigma\cdot x\in N$ for every $\sigma\in\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ and every $x\in N$, and assumed neither $\bot$ nor $\top$. Then one of the following holds: either for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, every $\sigma$ in the image in $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ fixes every $x\in N$; or for every such $A$ and every such $\sigma$ one has $\sigma\cdot x-x\in N$ for all $x\in E[p]$. The two alternatives are a disjunction, uniform in $A$; exclusivity is not asserted.
--
--   In classical terms: if the mod $p$ representation attached to the Frey curve has a proper nonzero stable submodule, then one of the two diagonal characters is unramified at $p$, the other being the mod $p$ cyclotomic character; this is the local input at $p$ to Mazur's irreducibility argument. It feeds the fixed-or-cofixed dichotomy [`FreyPackage.frey_stable_submodule_fixed_or_cofixed`](thm.html#FreyPackage.frey_stable_submodule_fixed_or_cofixed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem FreyPackage.frey_inertia_at_p_trivial_on_submodule_or_quotient (P : FreyPackage) (N : Submodule (ZMod P.p) (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p)) (hN : IsGaloisStable (K := AlgebraicClosure ℚ) ℚ N) (hbot : N ≠ ⊥) (htop : N ≠ ⊤) : (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime P.p → ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ N, σ • x = x) ∨ (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime P.p → ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p, σ • x - x ∈ N) := by sorry
