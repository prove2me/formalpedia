-- Prove2me | Theorems.Thm_FreyPackage_frey_torsion_fixed_eq_zero
-- name    : FreyPackage.frey_torsion_fixed_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/6dc50b87-919a-50af-b8a8-bfa9a8b8e413
-- title:
--   Galois-fixed p-torsion of the Frey curve vanishes
-- statement:
--   Let $P$ be a Frey package: nonzero integers $a,b,c$, a prime $p\ge 5$, with $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3\pmod 4$ and $b\equiv 0\pmod 2$. Let $E=P.\mathtt{freyCurve}$ be the associated Weierstrass curve over $\mathbb{Q}$ given by the coefficients $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$. Consider the group of affine points of $E$ base changed to $\overline{\mathbb{Q}}=\mathtt{AlgebraicClosure}\ \mathbb{Q}$, and inside it the $\mathbb{Z}$-submodule of elements annihilated by $(p:\mathbb{Z})$, i.e. $E[p](\overline{\mathbb{Q}})$. The assertion is: if $x$ is an element of this $p$-torsion submodule such that $\sigma\cdot x = x$ for every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$ (the action being the coordinatewise Galois action on points), then $x=0$. Equivalently, $E[p](\overline{\mathbb{Q}})^{G_{\mathbb{Q}}}=0$: the Frey curve has no nonzero $p$-torsion point defined over $\mathbb{Q}$.
--
--   This is the vanishing of the Galois-invariant part of the $p$-torsion of the Frey curve, which rules out the branch of the reducibility analysis of $\bar\rho_{E,p}$ in which the invariant line is spanned by a rational point. It is used by [`FreyPackage.frey_reducible_hasCofixedLine`](thm.html#FreyPackage.frey_reducible_hasCofixedLine), where the reducible case is forced into the dual (cofixed) alternative.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_frey_torsion_fixed_eq_zero.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem FreyPackage.frey_torsion_fixed_eq_zero (P : FreyPackage) (x : Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p) (hx : ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), σ • x = x) : x = 0 := by sorry
