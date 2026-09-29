-- Prove2me | Theorems.Thm_FreyPackage_frey_inertia_at_two_trivial_on_stable_submodule
-- name    : FreyPackage.frey_inertia_at_two_trivial_on_stable_submodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/2be0cc54-6203-53b4-8aaa-4a35cd4934c8
-- title:
--   Inertia at 2 acts trivially on a stable line of Frey E[p]
-- statement:
--   Let $P$ be a Frey package: nonzero integers $a,b,c$ and a prime $p\ge 5$ with $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$ and $b\equiv 0\pmod 2$, and let $P.\mathrm{freyCurve}$ be the associated Weierstrass curve over $\mathbb{Q}$ with $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$. Work with the group of points of this curve base-changed to $\overline{\mathbb{Q}}=\mathrm{AlgebraicClosure}\ \mathbb{Q}$ and its $p$-torsion submodule $T=\{x : p\cdot x=0\}$, viewed as a module over $\mathbb{Z}/p$. Let $N\subseteq T$ be a $\mathbb{Z}/p$-submodule that is Galois stable in the sense that $\sigma\cdot x\in N$ for every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$ and every $x\in N$, and assume $N\ne\bot$ and $N\ne\top$. The conclusion is that for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $2$ a non-unit of $A$, and every $\sigma$ in the image in $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup of $A$ inside its decomposition subgroup over $\mathbb{Q}$, one has $\sigma\cdot x=x$ for all $x\in N$, and $\sigma\cdot x-x\in N$ for all $x\in T$.
--
--   This is the statement that, at a place above $2$, where the Frey curve has multiplicative reduction, both the sub-character and the quotient character cut out by a proper nonzero Galois-stable $\mathbb{F}_p$-submodule of $E[p]$ are unramified; equivalently inertia at $2$ acts trivially on $N$ and on $T/N$. It is a local input to [`FreyPackage.frey_stable_submodule_fixed_or_cofixed`](thm.html#FreyPackage.frey_stable_submodule_fixed_or_cofixed), which feeds the irreducibility step for the mod $p$ representation attached to the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_frey_inertia_at_two_trivial_on_stable_submodule.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem FreyPackage.frey_inertia_at_two_trivial_on_stable_submodule (P : FreyPackage) (N : Submodule (ZMod P.p) (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p)) (hN : IsGaloisStable (K := AlgebraicClosure ℚ) ℚ N) (hbot : N ≠ ⊥) (htop : N ≠ ⊤) : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 2 → ∀ σ ∈ A.inertiaSubgroupIn ℚ, (∀ x ∈ N, σ • x = x) ∧ (∀ x : Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p, σ • x - x ∈ N) := by sorry
