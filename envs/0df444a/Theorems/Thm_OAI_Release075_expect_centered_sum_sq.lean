-- Prove2me | Theorems.Thm_OAI_Release075_expect_centered_sum_sq
-- name    : OAI.Release075.expect_centered_sum_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:39:39.303752+00:00
-- url     : https://prove2.me/theorems/12f95643-cf7e-4062-85cf-3910dc85553c
-- title:
--   Variance of a sum of independent coordinates
-- statement:
--   Here $\mathbb E$ denotes the average over all functions $\omega:I\to D$, i.e. the uniform product distribution on $D^I$ for finite nonempty $D$. Let $b:I\times D\to\mathbb R$ and $p_i=\mathbb E_d\,b_i(d)$. Then
--   $$
--   \mathbb E_\omega\Bigl[\Bigl(\sum_ib_i(\omega_i)-\sum_ip_i\Bigr)^2\Bigr]=\sum_i\mathbb E_d\bigl[(b_i(d)-p_i)^2\bigr].
--   $$
--
--   The variance of a sum of independent terms is the sum of the variances.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Incidence.lean#L72-L99

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence

open OAI OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem OAI.Release075.expect_centered_sum_sq {I D : Type*} [Fintype I] [DecidableEq I]
    [Fintype D] [Nonempty D] (b : I → D → ℝ) (p : I → ℝ)
    (hp : ∀ i, (𝔼 d, b i d) = p i) :
    (𝔼 ω : I → D, ((∑ i, b i (ω i)) - ∑ i, p i)^2) =
      ∑ i, (𝔼 d, (b i d - p i)^2) := by sorry
