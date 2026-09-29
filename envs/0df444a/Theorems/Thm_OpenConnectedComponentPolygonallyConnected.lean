-- Prove2me | Theorems.Thm_OpenConnectedComponentPolygonallyConnected
-- name    : OpenConnectedComponentPolygonallyConnected
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T23:54:34.176203+00:00
-- url     : https://prove2.me/theorems/85e7ddff-0c09-4fa0-bf87-5d56da22954b
-- title:
--   OpenConnectedComponentPolygonallyConnected
-- statement:
--   Every connected component of the complement of an open set in the Euclidean plane is polygonally path connected: any two points in the component can be joined by a polygonal path contained in that component.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/OpenConnectedComponentPolygonallyConnected.lean#L1-102

import Definitions.Def_ComplementComponent
import Definitions.Def_PolygonallyPathConnected

lemma OpenConnectedComponentPolygonallyConnected
    (U C : Set (EuclideanSpace ℝ (Fin 2))) :
    IsOpen U → ComplementComponent Uᶜ C → PolygonallyPathConnected C := by sorry
