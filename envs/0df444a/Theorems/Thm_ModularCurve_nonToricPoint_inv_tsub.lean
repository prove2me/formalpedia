-- Prove2me | Theorems.Thm_ModularCurve_nonToricPoint_inv_tsub
-- name    : ModularCurve.nonToricPoint_inv_tsub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/5ad1148b-9e06-51ef-8908-dff50477c790
-- title:
--   Inverting the Tate parameter negates the point
-- statement:
--   Let $K$ be a commutative ring, let $p, j$ be natural numbers with $0 < j$ and $j < p$, and let $c \in K^\times$. For a unit $c$ and an exponent $j$, `nonToricPoint K p c j` denotes the pair of Laurent series over $K$ obtained by substituting the family `slotFamily K p c j` of power series into the two universal integral power series `tateUnivX`, `tateUnivY` in two variables and viewing the resulting power series as Laurent series. Here `tateUnivX` assigns to an exponent vector $e$ the coefficient $-2\sum_{d \mid e_1} d$ when $e_0 = e_1$, and otherwise, with $n = |e_0 - e_1|$, the value $n$ if $n \mid e_1$ and $0$ if not; `tateUnivY` assigns $\sum_{d \mid e_1} d$ when $e_0 = e_1$, and otherwise, again with $n = |e_0 - e_1|$ and only when $n \mid e_1$, the value $\binom{n}{2}$ if $e_1 < e_0$ and $-\binom{n+1}{2}$ if $e_0 < e_1$, and $0$ when $n \nmid e_1$. Writing $(x, y) =$ `nonToricPoint K p c j`, the assertion is the equality of pairs of Laurent series $$\mathrm{nonToricPoint}\,K\,p\,c^{-1}\,(p - j) = (x,\; -y - x),$$ with $p - j$ the truncated difference of natural numbers.
--
--   This is the compatibility of the Tate parametrisation with inversion, read coefficientwise on the explicit $q$-expansions: the point with parameter $c^{-1}q^{p-j}$ is the negative of the point with parameter $cq^{j}$ on a curve in the Tate normal form $a_1 = 1$, $a_3 = 0$, where negation sends $(x,y)$ to $(x,-y-x)$. It is used in the construction of bases of the $p$-torsion attached to cusp data, in [`ModularCurve.torsion_basis_of_map_eq_variableChange_tateBase_cuspData`](thm.html#ModularCurve.torsion_basis_of_map_eq_variableChange_tateBase_cuspData) and [`ModularCurve.torsion_basis_of_map_eq_variableChange_tateBase_cuspData_of_mul_eq`](thm.html#ModularCurve.torsion_basis_of_map_eq_variableChange_tateBase_cuspData_of_mul_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_nonToricPoint_inv_tsub.lean

import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.nonToricPoint_inv_tsub {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ)
    (hj : 0 < j) (hjp : j < p) :
    nonToricPoint K p c⁻¹ (p - j) =
      ((nonToricPoint K p c j).1, -(nonToricPoint K p c j).2 - (nonToricPoint K p c j).1) := by sorry
