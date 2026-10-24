-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_inner_self_pos_of_comp_eq_id_408915f
-- name    : FunctionalInequalities.Analysis.inner_self_pos_of_comp_eq_id_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:24:51.428242+00:00
-- url     : https://prove2.me/theorems/7233d287-30b6-4835-b39c-8c207c6864f1
-- title:
--   Positivity Of A Right Inverse
-- statement:
--   This statement shows that a right inverse of a strictly positive operator is strictly positive.
--
--   Let E be a real inner-product normed additive group, and let T and B be continuous linear endomorphisms of E. Assume
--
--   1. for every nonzero v, $\langle Tv,v\rangle>0$;
--   2. $T\circ B=\operatorname{id}_E$.
--
--   Then for every nonzero v,
--
--   $$\langle Bv,v\rangle>0.$$
--
--   The result is a generic operator-positivity lemma applicable to right inverses, without a finite-dimensional assumption.
--
--   **Formalization Note** The inner products are real-valued and the conclusion is strict positivity for every vector explicitly assumed nonzero.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Operator/Positive.lean#L61-L76 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Operator.Positive`, declaration `FunctionalInequalities.Analysis.inner_self_pos_of_comp_eq_id`; the repository is private at upload time).

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach

open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.inner_self_pos_of_comp_eq_id_408915f (T B : E →L[ℝ] E)
    (hpos : ∀ v : E, v ≠ 0 → 0 < ⟪T v, v⟫)
    (hTB : T.comp B = ContinuousLinearMap.id ℝ E) {v : E} (hv : v ≠ 0) :
    0 < ⟪B v, v⟫ := by sorry
