-- Prove2me | Theorems.Thm_OpenConnectedComponentPolygonallyConnectedBundled
-- name    : OpenConnectedComponentPolygonallyConnectedBundled
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:41:18.316737+00:00
-- url     : https://prove2.me/theorems/871f8c66-bc37-426f-9d4d-9132f04bb13e
-- title:
--   Open Connected Component Polygonally Connected Bundled
-- statement:
--   Let $U\subseteq\mathbb R^2$ be open, and let $C$ be a connected component
--   of $U$.  Then $C$ is polygonally path connected.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `OpenConnectedComponentPolygonallyConnectedBundled`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/OpenConnectedComponentPolygonallyConnected.lean#L1-L102

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_PlaneFaceData
import Definitions.Def_PolygonallyPathConnected

lemma OpenConnectedComponentPolygonallyConnectedBundled
    (U C : Set (EuclideanSpace ℝ (Fin 2))) :
    IsOpen U → ComplementComponent Uᶜ C → PolygonallyPathConnected C := by sorry
