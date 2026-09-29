-- Prove2me | Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_two
-- name    : ModularCurve.eq_zero_of_mem_ssJSet_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/6336bf11-7092-5f9c-9873-59ebfed6edf1
-- title:
--   Characteristic 2: only j=0 in 𝔽₄ is supersingular
-- statement:
--   Let $k$ be a field of characteristic $2$ (with decidable equality), and let $a \in k$ satisfy two hypotheses. First, $a$ lies in $\mathrm{ssJSet}\,2\,k$, that is: for every Weierstrass curve $W$ over $k$ which is elliptic and whose $j$-invariant equals $a$, every point $P$ of the affine point group of $W$ with $2 \cdot P = 0$ is already $0$ — in other words no curve with $j$-invariant $a$ has a nonzero $k$-rational $2$-torsion point. Second, $a^{2^2} = a$, i.e. $a^4 = a$, so that $a$ lies in the copy of $\mathbb{F}_4$ inside $k$. The conclusion is $a = 0$. Thus among the elements of $\mathbb{F}_4 \subseteq k$, the only candidate $j$-invariant with the stated vanishing of rational $2$-torsion is $j = 0$; no assertion is made here that $j = 0$ does have this property.
--
--   This is the $q = 2$ half of the identification of the supersingular $j$-invariants in small characteristic, where the notion of supersingularity is taken in the concrete form 'no nonzero rational $2$-torsion on any curve with this $j$-invariant'. It is used in the analysis of the supersingular points of $X_0(q)$ for small $q$, where $j \in \{0, 1728\}$ are the only relevant values, and is cited by the local computations at the nodes in the Igusa-style models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_zero_of_mem_ssJSet_two.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.eq_zero_of_mem_ssJSet_two
    {k : Type*} [Field k] [CharP k 2] [DecidableEq k]
    (a : k) (ha : a ∈ ssJSet 2 k) (ha2 : a ^ (2 ^ 2) = a) : a = 0 := by sorry
