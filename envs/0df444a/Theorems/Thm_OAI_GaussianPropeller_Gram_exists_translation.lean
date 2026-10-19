-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Gram_exists_translation
-- name    : OAI.GaussianPropeller.Gram.exists_translation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T05:59:52.463217+00:00
-- url     : https://prove2.me/theorems/13fbf030-b294-48b6-bd3a-b63da73581b7
-- title:
--   A dual vector separating one obtuse vector from the others
-- statement:
--   Let $E$ be a finite-dimensional real inner product space and $z_j$, $j\in\iota$, finitely many vectors with $\sum_jz_j=0$ and $\langle z_j,z_l\rangle<0$ for $j\ne l$. For every index $i$ there is $h$ in the span of the $z_j$ with
--   $$
--   \langle h,z_i-z_j\rangle=1\quad(j\ne i),\qquad \langle h,z_i\rangle=\frac{|\iota|-1}{|\iota|}.
--   $$
--
--   Translating along $h$ moves the boundary of the cell of $z_i$ at the same rate on every face, which is how cell masses are differentiated.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Gram.lean#L148-L180

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion

open OAI OAI.GaussianPropeller
universe uE uF uι
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
variable {ι : Type uι} {E : Type uE} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem OAI.GaussianPropeller.Gram.exists_translation [FiniteDimensional ℝ E] (z : ι → E)
    (hneg : Pairwise (fun i j => ⟪z i, z j⟫ < 0)) (hsum : ∑ i, z i = 0)
    (i : ι) : ∃ h ∈ Submodule.span ℝ (Set.range z),
      (∀ j, j ≠ i → ⟪h, z i - z j⟫ = 1) ∧
        ⟪h, z i⟫ = ((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ) := by sorry
