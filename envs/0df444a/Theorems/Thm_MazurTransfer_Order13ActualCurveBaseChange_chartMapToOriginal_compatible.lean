-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualCurveBaseChange_chartMapToOriginal_compatible
-- name    : MazurTransfer.Order13ActualCurveBaseChange.chartMapToOriginal_compatible
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T03:23:07.035146+00:00
-- url     : https://prove2.me/theorems/881de298-5070-4111-83c6-d1f3b1f053e4
-- title:
--   The actual chart base-change maps satisfy gluing compatibility
-- statement:
--   Let $R$ and $S$ be commutative rings with an $R$-algebra structure on $S$. For each actual chart $i$ of the order-thirteen curve, let $\delta_i:C_{S,i}\to C_R$ be the specified chart base-change morphism followed by the original chart inclusion. For distinct charts $i,j$, these maps agree on their overlap:
--   $$\delta_i\circ\iota_{ij}=\delta_j\circ\iota_{ji}\circ t_{ij},$$
--   where $\iota_{ij}$ and $\iota_{ji}$ are the actual overlap inclusions and $t_{ij}$ is the specified reciprocal transition.
--
--   This compatibility supplies the input to the gluing-morphism constructor and defines the actual whole-curve base-change map.
-- source:
--   Unchanged target proof and six helper proof bodies from checked MazurTheorem Order13ActualCurveChangeOfBaseMorphism.lean, chartMapToOriginal_compatible, lines 103–120. Exact Lean oracle ranges preserve declarations, generated reassociation lemmas and section binders; proof helpers are isolated in a distinct namespace with the original actual chart family opened explicitly. The two transition naturality inputs forward to the separate Proved public theorem. Vas and contributors, Apache-2.0.

import Definitions.Def_MazurTransfer_Order13BaseChangeChartMorphisms
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13ActualCurveBaseChange
universe u

theorem MazurTransfer.Order13ActualCurveBaseChange.chartMapToOriginal_compatible (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (i j : Chart.{u}) (h : i ≠ j) :
    overlapInclusion S i j h ≫ chartMapToOriginal R S i =
      overlapTransition S i j h ≫ overlapInclusion S j i h.symm ≫ chartMapToOriginal R S j  := by sorry
