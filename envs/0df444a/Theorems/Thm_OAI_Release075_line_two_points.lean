-- Prove2me | Theorems.Thm_OAI_Release075_line_two_points
-- name    : OAI.Release075.line_two_points
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:43:47.70683+00:00
-- url     : https://prove2.me/theorems/d9cbf9bb-c7bb-43f5-beb7-cc0a26363794
-- title:
--   Two points on a line determine its direction and its marks
-- statement:
--   Let $V$ be a vector space over a field $K$, $a\in V$ a mark and $d$ a projective direction with representative $\hat d$. Suppose two distinct points $z\ne z'$ both lie on the line $\{a+t\hat d\}$. Then the direction is $d=[z'-z]$, and the mark lies on the line through them:
--   $$
--   a=z+t(z'-z)\quad\text{for some }t\in K .
--   $$
--
--   In particular the line carrying a mark is determined by any two of its points.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Incidence.lean#L468-L483

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence

open OAI OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem OAI.Release075.line_two_points (a z z' : V) (d : Projectivization K V) (hzz : z' ≠ z)
    (hz : OnChosenLine a z d) (hz' : OnChosenLine a z' d) :
    ∃ t : K, a = z + t • (z'-z) ∧
      d = Projectivization.mk K (z'-z) (sub_ne_zero.mpr hzz) := by sorry
