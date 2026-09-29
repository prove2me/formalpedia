-- Prove2me | Theorems.Thm_ModularCurve_diamondOneBar_comm
-- name    : ModularCurve.diamondOneBar_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/cf2e396b-9454-578d-aa14-ab4988bdb731
-- title:
--   Diamond operators on J₁(M) commute
-- statement:
--   Let $M$, $d$, $e$ be natural numbers, with no positivity, coprimality or other hypothesis imposed on them. Write $J$ for [`ModularCurve.JOne M`](def/ModularCurve_X1.html#L186), the group $\mathrm{Pic}^0$ of the function field `x1FunctionFieldBar M` of $X_1(M)$ over $\overline{\mathbb{Q}}$, i.e. the degree-zero divisor class group of that field regarded as a function field over the algebraic closure of $\mathbb{Q}$. For a natural number $d$, [`ModularCurve.diamondOneBar M d`](def/ModularCurve_X1Diamond.html#L98) is the $\mathbb{Z}$-linear endomorphism of $J$ obtained as follows: the $\overline{\mathbb{Q}}$-algebra automorphism `diamondAutBar M d` of `x1FunctionFieldBar M`, namely the base change to $\overline{\mathbb{Q}}$ of the diamond automorphism `diamondAut M d` of the function field over $\mathbb{Q}$, is viewed as the semilinear automorphism whose field component is its underlying ring automorphism and whose base component is the identity of $\overline{\mathbb{Q}}$; the distributive action of semilinear automorphisms on divisor classes then gives an additive, hence $\mathbb{Z}$-linear, endomorphism of $J$. The theorem asserts the equality of the two composites in the endomorphism ring of $J$: the endomorphism induced by $\langle d\rangle$ followed by the one induced by $\langle e\rangle$ equals the one induced by $\langle e\rangle$ followed by the one induced by $\langle d\rangle$.
--
--   This is the commutation of two diamond operators in the standard list of commutation relations among Hecke and diamond operators on the Jacobian $J_1(M)$. It is used as one component of [`ModularCurve.heckeDiamondCommuteBar`](thm.html#ModularCurve.heckeDiamondCommuteBar), which records the pairwise commutation of the Hecke and diamond operators on $J$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_diamondOneBar_comm.lean

import Mathlib
import Definitions.Def_ModularCurve_X1Diamond

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.diamondOneBar_comm (M d e : ℕ) :
    ModularCurve.diamondOneBar M d * ModularCurve.diamondOneBar M e =
      ModularCurve.diamondOneBar M e * ModularCurve.diamondOneBar M d := by sorry
