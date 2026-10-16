-- Prove2me | Theorems.Thm_OAI_ThreeManifold_GlobalAssembly_passages_disjoint
-- name    : OAI.ThreeManifold.GlobalAssembly.passages_disjoint
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:43:26.16658+00:00
-- url     : https://prove2.me/theorems/b91ff0db-a083-41cc-831d-171edfad4b56
-- title:
--   Distinct connected components of a subset of $\mathbb{R}$ are disjoint
-- statement:
--   Let $U \subseteq \mathbb{R}$ be any subset. For $x \in U$ let $\mathcal{C}_U(x)$ denote the connected component of $x$ in $U$, i.e. the largest connected subset of $U$ containing $x$. A *passage* of $U$ is a set of the form $\mathcal{C}_U(x)$ for some $x \in U$.
--
--   **Theorem.** Distinct passages of $U$ are disjoint: for passages $J$ and $K$ of $U$,
--   $$
--   J \neq K \ \Longrightarrow\ J \cap K = \varnothing .
--   $$
--
--   When $U$ is the open set of parameters at which a geodesic runs through a special region, its passages are the maximal open intervals of time spent there. Disjointness is what allows an integral over $U$ to be split as a sum over passages.
--
--   **Formalization Note** Passages are the elements of the subtype `Passages U`, and the statement is `Pairwise (Disjoint on (fun J => J.val))`; no hypothesis on $U$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Index.lean#L1274-L1286

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning
import Definitions.Def_OAI_Geometry_ConjugatePoints_Index

open OAI OAI.ThreeManifold OAI.ThreeManifold.GlobalAssembly
open Set MeasureTheory Topology Function

theorem OAI.ThreeManifold.GlobalAssembly.passages_disjoint (U : Set ℝ) : Pairwise (Disjoint on (fun J : Passages U => J.val)) := by sorry
