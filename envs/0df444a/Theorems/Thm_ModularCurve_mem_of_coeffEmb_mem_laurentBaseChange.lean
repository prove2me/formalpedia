-- Prove2me | Theorems.Thm_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange
-- name    : ModularCurve.mem_of_coeffEmb_mem_laurentBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/ca52a776-4cfa-53eb-bb35-0661a9122a29
-- title:
--   Descent of rational Laurent series from L· F₀
-- statement:
--   Let $L$ be a field equipped with an algebra structure over $\mathbb{Q}$, let $F_0$ be an intermediate field of $\mathbb{Q}((q))/\mathbb{Q}$, i.e. a subfield of the field of Laurent series $\mathbb{Q}((q))$ containing $\mathbb{Q}$, and let $x \in \mathbb{Q}((q))$. Write `coeffEmb L` for the ring homomorphism $\mathbb{Q}((q)) \to L((q))$ obtained by applying $\operatorname{algebraMap} \mathbb{Q} L$ to each coefficient (the map `coeffMap` attached to the structure morphism), and `laurentBaseChange L F₀` for the intermediate field of $L((q))/L$ generated over $L$ by the image of $F_0$ under this map, namely $L(\,\mathrm{coeffEmb}\,L\,(F_0)\,) = \mathrm{IntermediateField.adjoin}\,L$ applied to that image. The assertion is: if $\mathrm{coeffEmb}\,L\,(x)$ belongs to this compositum, then $x$ already belongs to $F_0$. No further hypothesis is imposed on $L$, on $F_0$, or on $x$; together with the evident reverse inclusion this says that the compositum of $L$ with the image of $F_0$ meets the rational-coefficient Laurent series exactly in (the image of) $F_0$.
--
--   This is the linear-disjointness (descent) step which guarantees that a Laurent series with rational coefficients lying in the field generated over $L$ by a rational subfield $F_0$ — typically $L = \mathbb{C}$ and $F_0$ the function field of a modular curve over $\mathbb{Q}$ — lies in $F_0$ itself, so that results proved after extension of the coefficient field can be brought back to $\mathbb{Q}((q))$. It is used in the treatment of $q$-expansions of modular curves and cusp forms, for instance to produce rational families and embedding bases and to identify differentials with prescribed $q$-expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Complex.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.mem_of_coeffEmb_mem_laurentBaseChange (L : Type*) [Field L] [Algebra ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (x : LaurentSeries ℚ)
    (hx : ModularCurve.coeffEmb L x ∈ ModularCurve.laurentBaseChange L F₀) : x ∈ F₀ := by sorry
