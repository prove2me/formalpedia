-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_sum_filter_eq_two_mul_sum_filter_of_compl_invariant_408915f
-- name    : FunctionalInequalities.Analysis.sum_filter_eq_two_mul_sum_filter_of_compl_invariant_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:04:35.400714+00:00
-- url     : https://prove2.me/theorems/81f2d525-0e90-4b2c-a20f-e31afe52b54f
-- title:
--   Complement Pairing of Boolean Mask Sums
-- statement:
--   This is a finite-sum pairing identity for Boolean masks.
--
--   Let $P$ be a predicate on masks $q:\operatorname{Fin}(m)\to\{\mathrm{false},\mathrm{true}\}$, assume $P(q)$ is equivalent to $P(\neg q)$, and let $f$ assign a real number to each mask with $f(\neg q)=f(q)$. For any fixed $i_0\in\operatorname{Fin}(m)$,
--
--   $$\sum_{q:\,P(q)}f(q)=2\sum_{q:\,q(i_0)=\mathrm{true}\ \wedge\ P(q)}f(q).$$
--
--   The identity pairs every mask with its complement and is used to restrict symmetric subset sums to representatives containing a chosen slot.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/IteratedDerivative/Bilinear.lean#L116-L166 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.IteratedDerivative.Bilinear`, declaration `FunctionalInequalities.Analysis.sum_filter_eq_two_mul_sum_filter_of_compl_invariant`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Data.List.FinRange

noncomputable section
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem FunctionalInequalities.Analysis.sum_filter_eq_two_mul_sum_filter_of_compl_invariant_408915f {m : ℕ} (P : (Fin m → Bool) → Prop)
    [DecidablePred P] (hP : ∀ q, P (fun i => !(q i)) ↔ P q) (f : (Fin m → Bool) → ℝ)
    (hf : ∀ q, f (fun i => !(q i)) = f q) (i₀ : Fin m) :
    ∑ q ∈ Finset.univ.filter P, f q = 2 * ∑ q ∈ Finset.univ.filter (fun q => q i₀ = true ∧ P q), f q := by sorry
