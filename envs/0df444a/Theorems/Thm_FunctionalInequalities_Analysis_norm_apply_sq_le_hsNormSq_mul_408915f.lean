-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_norm_apply_sq_le_hsNormSq_mul_408915f
-- name    : FunctionalInequalities.Analysis.norm_apply_sq_le_hsNormSq_mul_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:26:24.51329+00:00
-- url     : https://prove2.me/theorems/9d1a0f39-81a3-46f0-9f36-2262e81943b9
-- title:
--   Hilbert–Schmidt Bound On Operator Application
-- statement:
--   This statement bounds the norm of an operator applied to a vector.
--
--   Let n be a natural number, let M be a continuous linear endomorphism of $\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin} n)$, and let x be a vector. Then
--
--   $$\|Mx\|^2\leq\|M\|_{HS}^2\,\|x\|^2,$$
--
--   where `hsNormSq M` is the squared Hilbert–Schmidt norm.
--
--   This is a standard finite-dimensional estimate useful for Lyapunov and cutoff bounds.
--
--   **Formalization Note** The statement uses the canonical Euclidean basis and includes all natural numbers n.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Operator/HilbertSchmidt.lean#L75-L103 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Operator.HilbertSchmidt`, declaration `FunctionalInequalities.Analysis.norm_apply_sq_le_hsNormSq_mul`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.norm_apply_sq_le_hsNormSq_mul_408915f (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ‖M x‖ ^ 2 ≤ hsNormSq M * ‖x‖ ^ 2 := by sorry
