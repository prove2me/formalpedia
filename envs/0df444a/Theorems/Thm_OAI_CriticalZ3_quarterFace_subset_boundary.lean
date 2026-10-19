-- Prove2me | Theorems.Thm_OAI_CriticalZ3_quarterFace_subset_boundary
-- name    : OAI.CriticalZ3.quarterFace_subset_boundary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:48:25.967813+00:00
-- url     : https://prove2.me/theorems/786b6225-91c8-47e5-b97e-712d952861bd
-- title:
--   Quarter-faces lie in the cube boundary
-- statement:
--   For a centre $c\in\mathbb Z^3$ and $n\in\mathbb N$, the cube $\Lambda_n(c)$ has boundary the points with some coordinate $c_i\pm n$; it is the union of $24$ quarter-faces, each lying in one face plane $x_k=c_k\pm n$ with the other coordinates in a fixed half-range $[c_i,c_i+n]$ or $[c_i-n,c_i]$. Every quarter-face is contained in the boundary:
--   $$
--   \mathrm{QF}_f(c,n)\subseteq\partial\Lambda_n(c).
--   $$
--
--   Quarter-faces overlap along their edges, which is harmless for union bounds.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/QuarterFaces.lean#L23-L37

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

theorem OAI.CriticalZ3.quarterFace_subset_boundary (c : Vertex) (n : ℕ) (f : FaceIndex) :
    QuarterFace c n f ⊆ cubeBoundary c n := by sorry
