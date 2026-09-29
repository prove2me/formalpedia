-- Prove2me | Theorems.Thm_ModularCurve_slotSubst_gen_injective
-- name    : ModularCurve.slotSubst_gen_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/a92eaa79-3490-5af8-8261-f74c583d4864
-- title:
--   Injectivity of the slot substitution at p=2, j=1
-- statement:
--   Write $K = \mathrm{LaurentSeries}\,\mathbb{Q}$, the field of formal Laurent series over $\mathbb{Q}$, and let $r \in K^{\times}$ be the unit whose underlying Hahn series is the single term $1$ in degree $1$ (the Laurent variable), made a unit by the fact that this single-term series is nonzero. The theorem concerns the map `slotSubst` at the parameters $K$, $p = 2$, $c = r$ and $j = 1$: by definition it sends a two-variable formal power series $f \in \mathbb{Z}[[a,b]]$, i.e. an element of `MvPowerSeries (Fin 2) ℤ`, to the one-variable power series over $K$ obtained by Mathlib's multivariate substitution along the family `slotFamily`, whose two entries at these parameters are $C(r)\,X^{1}$ and $C(r^{-1})\,X^{2-1} = C(r^{-1})\,X$; thus $a \mapsto r\,q$ and $b \mapsto r^{-1} q$, the coefficients of $f$ being transported along the unique $\mathbb{Z}$-algebra structure on $K[[q]]$. There are no hypotheses. The assertion is that this map from $\mathbb{Z}[[a,b]]$ to $K[[q]]$ is injective as a function.
--
--   This is the statement that the two substituted monomials $rq$ and $r^{-1}q$ are algebraically independent enough for an integral two-variable power series to be recovered from its image: the coefficient of $a^{i}b^{k}$ in $f$ is the coefficient of $r^{i-k}$ in the $q^{i+k}$-coefficient of the substituted series. It is used by [`ModularCurve.tateUniv_equation`](thm.html#ModularCurve.tateUniv_equation) and [`ModularCurve.toricPoint_equation`](thm.html#ModularCurve.toricPoint_equation), where a universal identity between power series in two variables is reduced to its specialisation under this one substitution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_slotSubst_gen_injective.lean

import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.slotSubst_gen_injective : Function.Injective (slotSubst (LaurentSeries ℚ) 2
      (Units.mk0 (HahnSeries.single (1 : ℤ) (1 : ℚ)) (HahnSeries.single_ne_zero one_ne_zero)) 1) := by sorry
