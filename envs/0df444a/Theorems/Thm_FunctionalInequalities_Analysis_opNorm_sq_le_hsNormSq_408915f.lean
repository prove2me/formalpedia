-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_opNorm_sq_le_hsNormSq_408915f
-- name    : FunctionalInequalities.Analysis.opNorm_sq_le_hsNormSq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:26:34.840206+00:00
-- url     : https://prove2.me/theorems/db24406c-651e-42c1-9a4e-0b785c70f362
-- title:
--   Operator Norm Bounded By Hilbert–Schmidt Norm
-- statement:
--   This statement compares two norms of a finite-dimensional operator.
--
--   Let M be a continuous linear endomorphism of $\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin} n)$. Then
--
--   $$\|M\|_{op}^2\leq\|M\|_{HS}^2,$$
--
--   where `hsNormSq M` denotes the squared Hilbert–Schmidt norm.
--
--   This is a basic norm comparison reusable in finite-dimensional operator estimates.
--
--   **Formalization Note** The result is stated for every natural number n and uses the operator norm supplied by the continuous-linear-map structure.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Operator/HilbertSchmidt.lean#L105-L121 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Operator.HilbertSchmidt`, declaration `FunctionalInequalities.Analysis.opNorm_sq_le_hsNormSq`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.opNorm_sq_le_hsNormSq_408915f (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ‖M‖ ^ 2 ≤ hsNormSq M := by sorry
