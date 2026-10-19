-- Prove2me | Theorems.Thm_OAI_CriticalZ3_Box_successBits_disjoint
-- name    : OAI.CriticalZ3.Box.successBits_disjoint
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:17:29.171992+00:00
-- url     : https://prove2.me/theorems/7b4f412a-3658-4787-bb61-287a37dcb5e7
-- title:
--   Success bits of separated entrants are disjoint
-- statement:
--   A box $B\subseteq\mathbb Z^3$ is a product of integer intervals; nearest neighbours differ by $\pm1$ in one coordinate. Let $C$ be a box wide enough for seed cubes of radius $r$, and let $y,z$ be exterior vertices of $C$ that are far apart in some coordinate, $|y_i-z_i|>4r+2$. Then their success bits are disjoint:
--   $$
--   \mathrm{succ}(y)\cap\mathrm{succ}(z)=\varnothing .
--   $$
--
--   Hence seed trials at separated entrants are independent.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/SeedTrials.lean#L88-L110

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials

open OAI OAI.CriticalZ3 OAI.CriticalZ3.Box
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical

theorem OAI.CriticalZ3.Box.successBits_disjoint (C : Box) (r : ℕ) (m : Model)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) {y z : Vertex}
    (hy : C.Exterior y) (hz : C.Exterior z) (hsep : ∃ i, (4*r+2 : ℤ) < |y i-z i|) :
    Disjoint (C.successBits r m y) (C.successBits r m z) := by sorry
