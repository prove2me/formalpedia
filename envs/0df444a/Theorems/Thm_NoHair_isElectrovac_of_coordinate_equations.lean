-- Prove2me | Theorems.Thm_NoHair_isElectrovac_of_coordinate_equations
-- name    : NoHair.isElectrovac_of_coordinate_equations
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T19:45:26.024823+00:00
-- url     : https://prove2.me/theorems/89c7e4da-033b-40c9-93e9-ecf4428a5a45
-- title:
--   Coordinate Einstein–Maxwell equations give electrovacuum on an open subset of $\mathbb R^4$
-- statement:
--   Let $U$ be an open subset of $\mathbb R^4$ with its induced atlas. Let $G$ and $F$ be matrix-valued functions on coordinate space, and give $U$ the bilinear fields whose coordinate matrices are their restrictions. Then
--
--   $$\bigl(\forall y\in U,\;\mathrm{EinsteinMaxwellAt}(G,F,y)\bigr)\;\Longrightarrow\;\mathrm{IsElectrovac}(G|_U,F|_U).$$
--
--   This identifies the coordinate and manifold formulations on an open coordinate domain, including the derivatives entering the Einstein tensor and the Maxwell divergence.
-- source:
--   Prove2Me, definitions NoHair_spacetime (pullbackCoeffs, IsElectrovac), https://prove2.me/definitions/bb86f59e-bd9c-4837-b65b-49b71e8d0e7b, and NoHair_kerrNewman (matrixBilin), https://prove2.me/definitions/f8c3d6a0-7b2a-491b-bc20-023abe056cae. Mathlib, TopologicalSpace.Opens.chart_eq, Mathlib/Geometry/Manifold/HasGroupoid.lean at 0df444a.

import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open NoHair Set

theorem NoHair.isElectrovac_of_coordinate_equations (U : TopologicalSpace.Opens E4)
    (G F : E4 → Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∀ y ∈ U, EinsteinMaxwellAt G F y) :
    IsElectrovac (M := U) (fun x => matrixBilin (G x.val)) (fun x => matrixBilin (F x.val)) := by sorry
