-- Prove2me | Theorems.Thm_MazurTransfer_closed_point_kernel_invertible_over_field
-- name    : MazurTransfer.closed_point_kernel_invertible_over_field
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-09T21:37:06.384054+00:00
-- url     : https://prove2.me/theorems/aa383dbb-2de6-418c-8f3d-01cb9aa9f65c
-- title:
--   Arbitrary closed points on a smooth integral curve have invertible kernel ideals
-- statement:
--   Let $X$ be an integral, locally noetherian scheme, smooth of relative dimension one over a field $k$. Let $P:\operatorname{Spec}L\hookrightarrow X$ be a closed immersion from any field $L$, which need not equal $k$. The actual ideal sheaf cutting out this closed point is invertible:
--   \[
--   \ker(P)\text{ is an invertible ideal sheaf on }X.
--   \]
--   This supplies the closed-point line bundles needed to realize arbitrary divisors, including divisors supported at nonrational points, in the arithmetic Picard correspondence. No algebraic-closure hypothesis or restriction to rational sections is imposed.
-- source:
--   Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0, https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . Separately checked arbitrary-residue-field adaptations by Vas and contributors, downstream MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0, https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Original theorem statements are preserved.

import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
open CategoryTheory AlgebraicGeometry

theorem MazurTransfer.closed_point_kernel_invertible_over_field.{u}
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (x : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 x]
    {L : Type u} [Field L] (P : Spec (CommRingCat.of L) ⟶ X) [IsClosedImmersion P] :
    P.ker.IsInvertible := by sorry
