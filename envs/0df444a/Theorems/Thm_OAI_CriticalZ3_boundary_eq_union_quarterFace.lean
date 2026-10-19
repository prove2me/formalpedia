-- Prove2me | Theorems.Thm_OAI_CriticalZ3_boundary_eq_union_quarterFace
-- name    : OAI.CriticalZ3.boundary_eq_union_quarterFace
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:49:00.109858+00:00
-- url     : https://prove2.me/theorems/2c74163a-e2ca-47c9-b816-d3c2f163a8dc
-- title:
--   The cube boundary is the union of the 24 quarter-faces
-- statement:
--   For a centre $c\in\mathbb Z^3$ and $n\in\mathbb N$, the cube $\Lambda_n(c)$ has boundary the points with some coordinate $c_i\pm n$; it is the union of $24$ quarter-faces, each lying in one face plane $x_k=c_k\pm n$ with the other coordinates in a fixed half-range $[c_i,c_i+n]$ or $[c_i-n,c_i]$. The boundary of the cube is exactly the union of its quarter-faces:
--   $$
--   \partial\Lambda_n(c)=\bigcup_f\mathrm{QF}_f(c,n).
--   $$
--
--   So reaching the boundary means reaching one of the $24$ quarter-faces.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/QuarterFaces.lean#L39-L55

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces

open OAI OAI.CriticalZ3
universe uE uI uV uW
open MeasureTheory ProbabilityTheory Classical
open Classical

theorem OAI.CriticalZ3.boundary_eq_union_quarterFace (c : Vertex) (n : ℕ) :
    cubeBoundary c n = ⋃ f : FaceIndex, QuarterFace c n f := by sorry
