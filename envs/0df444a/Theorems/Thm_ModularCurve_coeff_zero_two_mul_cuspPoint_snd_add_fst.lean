-- Prove2me | Theorems.Thm_ModularCurve_coeff_zero_two_mul_cuspPoint_snd_add_fst
-- name    : ModularCurve.coeff_zero_two_mul_cuspPoint_snd_add_fst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/dedce2ef-7aa3-528c-a084-86fb7b3a9bd4
-- title:
--   Constant term of 2yᵥ + xᵥ at Tate cusp points
-- statement:
--   Let $L$ be a field, let $N$ be a positive natural number, let $\xi \in L^\times$ be a unit whose underlying element is a primitive $N$-th root of unity in $L$, and let $v \colon \mathrm{Fin}\,2 \to \mathbb{Z}/N$ be a nonzero pair $(v_0, v_1)$. The pair of Laurent series [`ModularCurve.cuspPoint L N ξ v`](def/ModularCurve_KatzLevelPCusps.html#L59) over $L$ is, by definition, $\mathtt{tateToricPoint}$ at the unit $c = \xi^{\,(v_0).\mathrm{val}}$ when $v_1 = 0$ — whose two components are the power series (viewed as Laurent series, i.e. Hahn series over $\mathbb{Z}$) with constant coefficients $c\cdot\mathrm{inv}(1-c)^2$ and $c^2\cdot\mathrm{inv}(1-c)^3$ respectively and with explicit divisor-sum coefficients in positive degrees — and otherwise $\mathtt{nonToricPoint}$ at $c$ and the index $j = (v_1).\mathrm{val}$, whose components are the power series $\mathtt{slotSubst}\,L\,N\,c\,j$ applied to $\mathtt{tateUnivX}$ and to $\mathtt{tateUnivY}$. The assertion is that the coefficient in degree $0$ of the Laurent series $2\cdot(\text{second component}) + (\text{first component})$ equals $c\,(1+c)\,\bigl((1-c)^{-1}\bigr)^3$ with $c = \xi^{\,(v_0).\mathrm{val}}$ when $v_1 = 0$, and equals $0$ when $v_1 \neq 0$.
--
--   This computes the constant term of the combination $2y+x$ of the coordinates of the Tate-curve cusp points attached to $v \in (\mathbb{Z}/N)^2 \setminus \{0\}$: the toric cusps ($v_1 = 0$) contribute $c(1+c)/(1-c)^3$, while the remaining cusps contribute nothing because both coordinates have positive $q$-order there. It is used in the construction of weight-three forms whose $q$-expansions are the given cusp points, and in the identification of the action of the level automorphisms on such data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_zero_two_mul_cuspPoint_snd_add_fst.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.coeff_zero_two_mul_cuspPoint_snd_add_fst
    (L : Type) [Field L] (N : ℕ) [NeZero N] (ξ : Lˣ) (hξ : IsPrimitiveRoot (ξ : L) N)
    (v : Fin 2 → ZMod N) (hv : v ≠ 0) :
    (2 * (ModularCurve.cuspPoint L N ξ v).2 + (ModularCurve.cuspPoint L N ξ v).1).coeff 0 =
      if v 1 = 0 then ((ξ ^ (v 0).val : Lˣ) : L) * (1 + ((ξ ^ (v 0).val : Lˣ) : L)) * ((1 - ((ξ ^ (v 0).val : Lˣ) : L))⁻¹) ^ 3
      else 0 := by sorry
