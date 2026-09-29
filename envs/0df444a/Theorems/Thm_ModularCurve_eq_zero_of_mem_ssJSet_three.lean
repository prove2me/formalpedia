-- Prove2me | Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_three
-- name    : ModularCurve.eq_zero_of_mem_ssJSet_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/337da7fb-90c8-57a3-b244-9c9089123a93
-- title:
--   Supersingular j-invariants in 𝔽₉ vanish in characteristic 3
-- statement:
--   Let $k$ be a field of characteristic $3$ and let $a \in k$. Assume first that $a$ belongs to $\mathrm{ssJSet}\,3\,k$, that is: for every Weierstrass curve $W$ over $k$ which is elliptic (its discriminant is a unit) and whose $j$-invariant equals $a$, every point $P$ of the associated affine curve with $3 \cdot P = 0$ is the point at infinity. Assume second that $a^{3^2} = a$, i.e. $a^9 = a$, so that $a$ lies in the copy of $\mathbb{F}_9$ inside $k$. Then $a = 0$. Thus among the elements of $\mathbb{F}_9 \subseteq k$ the only one that can be a "supersingular" $j$-value in the above sense — the sense of having no nontrivial $k$-rational $3$-torsion on any elliptic curve of that $j$-invariant — is $j = 0$. Note that the hypothesis is a statement about all Weierstrass models with the given $j$-invariant, so the conclusion is obtained by exhibiting a single such model with a nontrivial $3$-torsion point.
--
--   This is the characteristic-$3$ half of the explicit determination of the supersingular $j$-values in the prime field's quadratic extension: in characteristic $3$ the supersingular $j$-invariant is $0$. It is used in the analysis of the supersingular points of the modular curve, for instance in the product formulae over $\mathrm{ssJSet}$ and in the local study at the nodes appearing in the Igusa-scheme computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_zero_of_mem_ssJSet_three.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.eq_zero_of_mem_ssJSet_three
    {k : Type*} [Field k] [CharP k 3] [DecidableEq k]
    (a : k) (ha : a ∈ ssJSet 3 k) (ha2 : a ^ (3 ^ 2) = a) : a = 0 := by sorry
