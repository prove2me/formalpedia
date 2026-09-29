-- Prove2me | Theorems.Thm_ModularCurve_eq_cuspInftyBar_of_mul_ord_eq
-- name    : ModularCurve.eq_cuspInftyBar_of_mul_ord_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/cfe1f1b1-f77a-5107-aba1-9bbfe17438c0
-- title:
--   A cusp of type N is the cusp at infinity
-- statement:
--   Let $N$ be a nonzero natural number and let $F_N =$ `modularFunctionFieldBar N` be the subfield of the Laurent series field $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise images under `coeffEmb` of the elements of `modularFunctionFieldFull N`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the family `divisorExpansions N`. Let $u$ be a place of $F_N$ over $\overline{\mathbb{Q}}$, that is, a valuation subring of $F_N$ which contains the image of $\overline{\mathbb{Q}}$, is not all of $F_N$, and is a principal ideal ring; write $u.\mathrm{ord}$ for the associated normalised integer valuation (minus the logarithm of the height-one adic valuation). Assume that $u.\mathrm{ord}$ of the element $j$ of $F_N$, given by the coefficientwise image of the Laurent series `jq` $= q^{-1}\cdot j_{\mathrm{num}}(q)$, is strictly negative, i.e. $j$ has a pole at $u$. Let $d$ be a natural number such that $$N \cdot u.\mathrm{ord}\bigl(j(q^N)\bigr) = d^2 \cdot u.\mathrm{ord}(j),$$ where $j(q^N)$ denotes the coefficientwise image of `qExpand ℚ N jq`, the substitution $q \mapsto q^N$ applied to `jq`, and suppose $d = N$. Then $u$ equals `cuspInftyBar N`, the $q$-adic place `qInftyPlaceBar` of $F_N$, whose valuation subring consists of the elements of nonnegative order and which is witnessed by the element $j$ having order $-1$.
--
--   Classically, at a cusp of $X_0(N)$ of denominator $c \mid N$ the ratio $\mathrm{ord}(j(q^N))/\mathrm{ord}(j)$ equals $c^2/N$, so the quantity $d$ occurring here is the denominator, or type, of the cusp, and the cusps of type $N$ reduce to the single cusp at infinity, where $\mathrm{ord}\,j = -1$ and $\mathrm{ord}\,j(q^N) = -N$. The statement is the identification step used by [`ModularCurve.eq_cuspInftyBar_of_isCusp_of_ord_jqN_eq_mul_ord_jq_of_neZero`](thm.html#ModularCurve.eq_cuspInftyBar_of_isCusp_of_ord_jqN_eq_mul_ord_jq_of_neZero) to single out the cusp at infinity among the places of the level-$N$ modular function field over $\overline{\mathbb{Q}}$ at which $j$ has a pole.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_cuspInftyBar_of_mul_ord_eq.lean

import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem ModularCurve.eq_cuspInftyBar_of_mul_ord_eq (N : ℕ) [NeZero N]
    (u : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hpole : u.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full N (jq_mem N))⟩ < 0)
    (d : ℕ)
    (hanchor : (N : ℤ) * u.ord ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩
        = (d : ℤ) ^ 2 * u.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩)
    (hd : d = N) :
    u = cuspInftyBar N := by sorry
