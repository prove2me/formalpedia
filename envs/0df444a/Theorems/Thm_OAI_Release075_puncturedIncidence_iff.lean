-- Prove2me | Theorems.Thm_OAI_Release075_puncturedIncidence_iff
-- name    : OAI.Release075.puncturedIncidence_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:40:41.007709+00:00
-- url     : https://prove2.me/theorems/6e1ee56f-be9d-4f89-8525-0ed851a09cd4
-- title:
--   A point off the mark lies on exactly one line direction
-- statement:
--   For marks $a\in V$ in a vector space over a field $K$ and a projective direction $d$ with chosen representative $\hat d$, the point $z$ is punctured-incident to the line $(a,d)$ when $z\ne a$ and $z=a+t\hat d$ for some $t\in K$. If $z\ne a$, then for every projective direction $d$,
--   $$
--   z\text{ is punctured-incident to }(a,d)\iff d=[z-a] .
--   $$
--
--   So a point different from a mark lies on exactly one of the lines through that mark.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Incidence.lean#L154-L170

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence

open OAI OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem OAI.Release075.puncturedIncidence_iff (a z : V) (hza : z ≠ a) (d : Projectivization K V) :
    PuncturedIncidence a z d ↔ d = Projectivization.mk K (z-a) (sub_ne_zero.mpr hza) := by sorry
