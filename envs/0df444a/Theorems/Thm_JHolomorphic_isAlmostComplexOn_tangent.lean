-- Prove2me | Theorems.Thm_JHolomorphic_isAlmostComplexOn_tangent
-- name    : JHolomorphic.isAlmostComplexOn_tangent
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T12:02:13.78645+00:00
-- url     : https://prove2.me/theorems/862cb55b-65fe-4870-8c71-d6063ffa8f71
-- title:
--   The tangent lift of an almost complex structure is almost complex
-- statement:
--   Let $E$ be a finite-dimensional real normed space and let $J$ be a smooth almost complex structure on an open set $O\subseteq E$, i.e. $J:O\to\mathrm{End}_{\mathbb R}(E)$ is $C^\infty$ and $J(x)^2=-\mathbb 1$ for $x\in O$. Define $J^T$ on $E\times E$ by
--   $$J^T(x,y)(a,b)=\big(J(x)a,\;J(x)b+DJ(x)[y]\,a\big).$$
--   Then $J^T$ is a smooth almost complex structure on the open set $O\times E\subseteq E\times E$.
--
--   $J^T$ is the almost complex structure induced by $J$ on the tangent bundle $TO=O\times E$ (the tangent lift of $J$).
--
--   **Formalization Note** The hypothesis and conclusion are `IsAlmostComplexOn` ($O$ open, $J$ is $C^\infty$ on $O$, $J(x)\circ J(x)=-\mathrm{id}$ on $O$). $DJ(x)[y]$ is `fderiv ℝ J x y`, and $J^T$ is written inline as the continuous linear map `((J x.1).comp fst).prod ((J x.1).comp snd + (fderiv ℝ J x.1 x.2).comp fst)`; the open set is `O ×ˢ Set.univ`. $E\times E$ carries the product norm.
-- source:
--   Standard (the almost complex structure on the tangent bundle induced by $J$).

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory
open scoped ContDiff

/-- The tangent almost complex structure: if `J` is a smooth almost complex structure on the open
set `O ⊆ E`, then `J^T(x, y)(a, b) = (J(x) a, J(x) b + DJ(x)[y] a)` is a smooth almost complex
structure on `O × E ⊆ E × E`. -/
theorem isAlmostComplexOn_tangent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E) (hJ : IsAlmostComplexOn J O) :
    IsAlmostComplexOn
      (fun x : E × E => ((J x.1).comp (ContinuousLinearMap.fst ℝ E E)).prod
        ((J x.1).comp (ContinuousLinearMap.snd ℝ E E) +
          (fderiv ℝ J x.1 x.2).comp (ContinuousLinearMap.fst ℝ E E)))
      (O ×ˢ Set.univ) := by
  sorry

end JHolomorphic
