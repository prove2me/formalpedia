-- Prove2me | Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldC_one_eq_zero
-- name    : ModularCurve.genusFF_modularFunctionFieldC_one_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/459a5953-5a82-5c05-bf42-6827a66fb9ff
-- title:
--   The level-one modular function field has genus zero
-- statement:
--   Let $k$ be a field which is perfect. Inside the field $\mathrm{LaurentSeries}\,k = k(\!(q)\!)$ consider the Laurent series $\mathtt{jqModC}\ k = q^{-1}\cdot \iota(\mathtt{jNum})$, where $\iota$ is the coefficientwise map induced by the ring homomorphism $\mathbb{Z} \to k$ applied to the integral power series $\mathtt{jNum}$, and the series $\mathtt{jqNModC}\ k\ 1 = \mathtt{qExpand}\ k\ 1$ applied to $\mathtt{jqModC}\ k$; let $\mathtt{modularFunctionFieldC}\ k\ 1$ be the intermediate field of $k(\!(q)\!)/k$ obtained by adjoining to $k$ these two elements. The assertion is that the invariant $\mathtt{genusFF}$ of this extension vanishes, i.e. that $$\dim_k H^1(0) = 0,$$ where $H^1(D)$ is the repartition (adèle) cohomology space attached to a divisor $D \in \mathrm{Place}\,k\,F \to_{f} \mathbb{Z}$ of the extension, $D$ here being the zero divisor, and $F = \mathtt{modularFunctionFieldC}\ k\ 1$. Thus the function field generated over a perfect field $k$ by the reduction of the $q$-expansion of the modular invariant has repartition genus $0$.
--
--   This is the level-one case of the genus computation for the characteristic-$p$ fibre function fields of the modular curves, the classical statement that $X_0(1)$ has genus zero with $j$ as a coordinate. It is used in the construction of models, component charts and annulus data for place specialisations of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_genusFF_modularFunctionFieldC_one_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.genusFF_modularFunctionFieldC_one_eq_zero (k : Type*) [Field k] [PerfectField k] :
    genusFF k ↥(modularFunctionFieldC k 1) = 0 := by sorry
