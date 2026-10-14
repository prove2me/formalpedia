-- Prove2me | Theorems.Thm_OAI_PiExponent_InterpolationMatrix_exists_full_row_minor_of_surjective
-- name    : OAI.PiExponent.InterpolationMatrix.exists_full_row_minor_of_surjective
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-11T12:11:20.84849+00:00
-- url     : https://prove2.me/theorems/f3ace940-1663-489e-af28-d1f63c803801
-- title:
--   A surjective matrix has a nonsingular full-row minor
-- statement:
--   Let $R$ and $C$ be finite index types, let $K$ be a field, and let $A=(A_{r,c})_{r\in R,\,c\in C}$ be an $R$-by-$C$ matrix over $K$. Assume equality on $R$ is decidable and multiplication by $A$ defines a surjective $K$-linear map $K^C\to K^R$. Then there is a function $s:R\to C$ such that $s$ is injective and
--
--   $$
--   \det\bigl(A[\operatorname{id}_R,s]\bigr)\ne 0.
--   $$
--
--   Thus the selected columns form a nonsingular square minor containing every row. This generic matrix-rank lemma is a direct core dependency for choosing a nonvanishing interpolation minor in the $\pi$ irrationality-measure argument.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/InterpolationMatrix.lean#L135-L166

import Mathlib

namespace OAI

open scoped BigOperators

namespace PiExponent.InterpolationMatrix

theorem exists_full_row_minor_of_surjective
    {R C K : Type*} [Fintype R] [Fintype C] [DecidableEq R] [Field K]
    (A : Matrix R C K) (hA : Function.Surjective A.mulVecLin) :
    ∃ selection : R → C, Function.Injective selection ∧
      (A.submatrix id selection).det ≠ 0 := by
  sorry

end PiExponent.InterpolationMatrix

end OAI
