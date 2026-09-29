-- Prove2me | Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_valuativeCriterion_existence_toCrossing
-- name    : MvPolynomial.CrossingQuotient.Resolution.valuativeCriterion_existence_toCrossing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/c4cb8cd8-f27f-53b4-a242-42cfa831cc2e
-- title:
--   Valuative existence for the resolution of uv=t^e
-- statement:
--   Let $W$ be a commutative ring, $t \in W$ and $e$ a natural number. Write $C_s$ for the ring $W[X_0,X_1]/(X_0X_1 - C(s))$, so that `crossingScheme s` is $\operatorname{Spec} C_s$; in particular the target is $\operatorname{Spec} \bigl(W[X_0,X_1]/(X_0X_1-t^e)\bigr)$. Let `Resolution t e` be the colimit of the diagram `glueDiagram t e` indexed by `GlueIndex e`, whose objects are the $e$ charts $\operatorname{Spec}\bigl(W[X_0,X_1]/(X_0X_1-t)\bigr)$ together with their overlaps and whose maps are the gluing morphisms `glueMap t e`, and let `Resolution.toCrossing t e` be the morphism $\operatorname{Resolution} \to \operatorname{Spec} C_{t^e}$ obtained from the universal property of the colimit applied to the cocone `crossingCocone t e` with vertex $\operatorname{Spec} C_{t^e}$ and components `crossingCoconeApp t e`. The assertion is that this morphism satisfies the existence half of the valuative criterion: for every valuation ring $O$ which is a domain with fraction field $K$, and every commutative square consisting of a morphism $\operatorname{Spec} K \to \operatorname{Resolution}(t,e)$, a morphism $\operatorname{Spec} O \to \operatorname{Spec} C_{t^e}$ and the morphism $\operatorname{Spec} K \to \operatorname{Spec} O$, there exists a morphism $\operatorname{Spec} O \to \operatorname{Resolution}(t,e)$ making both resulting triangles commute. No positivity hypothesis on $e$ is imposed.
--
--   This is the existence (lifting) part of the valuative criterion for the map from the glued resolution of the $e$-fold degeneration $uv = t^e$ to the singular affine scheme itself, the substantive ingredient in the proof that this morphism is proper; it is used by [`MvPolynomial.CrossingQuotient.Resolution.isProper_toCrossing`](thm.html#MvPolynomial.CrossingQuotient.Resolution.isProper_toCrossing). The lifting is reduced, via [`MvPolynomial.CrossingQuotient.exists_comp_resolutionChart_eq_of_valuationRing`](thm.html#MvPolynomial.CrossingQuotient.exists_comp_resolutionChart_eq_of_valuationRing), to the statement that a ring map from $W[u,v]/(uv-t^e)$ to a valuation ring factors through one of the $e$ charts $W[x,y]/(xy-t)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_CrossingQuotient_Resolution_valuativeCriterion_existence_toCrossing.lean

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

theorem MvPolynomial.CrossingQuotient.Resolution.valuativeCriterion_existence_toCrossing
    {W : Type u} [CommRing W] (t : W) (e : ℕ) :
    ValuativeCriterion.Existence (Resolution.toCrossing t e) := by sorry
