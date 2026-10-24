-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_sum_inner_apply_le_sqrt_hsNormSq_mul_408915f
-- name    : FunctionalInequalities.Analysis.sum_inner_apply_le_sqrt_hsNormSq_mul_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:26:25.394003+00:00
-- url     : https://prove2.me/theorems/abca67e4-bfc5-40c2-be71-32862325c056
-- title:
--   Hilbert–Schmidt Cauchy–Schwarz Bound
-- statement:
--   This statement gives the Cauchy–Schwarz inequality for the Hilbert–Schmidt pairing.
--
--   Let M and N be continuous linear endomorphisms of $\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin} n)$, and let $(e_j)$ be the canonical orthonormal basis. Then
--
--   $$\sum_j\langle Me_j,Ne_j\rangle
--   \leq\sqrt{\|M\|_{HS}^2}\,\sqrt{\|N\|_{HS}^2}.$$
--
--   This is the basis-coordinate form of Cauchy–Schwarz for Hilbert–Schmidt operators.
--
--   **Formalization Note** The square roots are real square roots of the nonnegative quantities `hsNormSq M` and `hsNormSq N`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Operator/HilbertSchmidt.lean#L158-L176 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Operator.HilbertSchmidt`, declaration `FunctionalInequalities.Analysis.sum_inner_apply_le_sqrt_hsNormSq_mul`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_HilbertSchmidt
import Mathlib
import Mathlib.Analysis.InnerProductSpace.Trace

noncomputable section
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {n : ℕ}

theorem FunctionalInequalities.Analysis.sum_inner_apply_le_sqrt_hsNormSq_mul_408915f (M N : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∑ j, ⟪M (EuclideanSpace.basisFun (Fin n) ℝ j), N (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ ≤
      Real.sqrt (hsNormSq M) * Real.sqrt (hsNormSq N) := by sorry
