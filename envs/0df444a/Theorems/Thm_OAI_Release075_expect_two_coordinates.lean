-- Prove2me | Theorems.Thm_OAI_Release075_expect_two_coordinates
-- name    : OAI.Release075.expect_two_coordinates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:38:57.857005+00:00
-- url     : https://prove2.me/theorems/030eec2e-8fd1-4bc7-b72f-f3c1e367ccc2
-- title:
--   Two distinct coordinates of a uniform function are independent
-- statement:
--   Here $\mathbb E$ denotes the average over all functions $\omega:I\to D$, i.e. the uniform product distribution on $D^I$ for finite nonempty $D$. For distinct $i\ne j$ in $I$ and functions $f,g:D\to\mathbb R$,
--   $$
--   \mathbb E_\omega\bigl[f(\omega_i)\,g(\omega_j)\bigr]=\mathbb E_d[f(d)]\cdot\mathbb E_d[g(d)] .
--   $$
--
--   So two distinct coordinates of a uniformly random function are uncorrelated in this sense.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Incidence.lean#L30-L49

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence

open OAI OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem OAI.Release075.expect_two_coordinates {I D : Type*} [Fintype I] [DecidableEq I] [Fintype D] [Nonempty D]
    (i j : I) (hij : i ≠ j) (f g : D → ℝ) :
    (𝔼 ω : I → D, f (ω i) * g (ω j)) = (𝔼 d, f d) * (𝔼 d, g d) := by sorry
