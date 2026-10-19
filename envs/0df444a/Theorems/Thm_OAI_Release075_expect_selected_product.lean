-- Prove2me | Theorems.Thm_OAI_Release075_expect_selected_product
-- name    : OAI.Release075.expect_selected_product
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:40:09.010343+00:00
-- url     : https://prove2.me/theorems/e1cd8254-7e90-46d3-9751-da2ec3846c87
-- title:
--   Product moments of injectively selected coordinates
-- statement:
--   Here $\mathbb E$ denotes the average over all functions $\omega:I\to D$, i.e. the uniform product distribution on $D^I$ for finite nonempty $D$. For an injection $e:A\hookrightarrow I$ from a finite set $A$ and functions $f_a:D\to\mathbb R$,
--   $$
--   \mathbb E_\omega\Bigl[\prod_{a\in A}f_a\bigl(\omega_{e(a)}\bigr)\Bigr]=\prod_{a\in A}\mathbb E_d\,f_a(d) .
--   $$
--
--   Distinct coordinates of a uniform function are jointly independent.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Incidence.lean#L124-L141

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence

open OAI OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem OAI.Release075.expect_selected_product {A I D : Type*} [Fintype A] [Fintype I]
    [DecidableEq I] [Fintype D] [Nonempty D]
    (e : A ↪ I) (f : A → D → ℝ) :
    (𝔼 ω : I → D, ∏ a, f a (ω (e a))) = ∏ a, 𝔼 d, f a d := by sorry
