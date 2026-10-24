-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_comp_perm_of_contDiff_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_comp_perm_of_contDiff_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:04:25.303092+00:00
-- url     : https://prove2.me/theorems/86ef9417-4e3a-4b36-88cb-66cacd2e632a
-- title:
--   Full Permutation Symmetry of Iterated Derivatives
-- statement:
--   This is the full permutation-symmetry theorem for iterated Fréchet derivatives of a smooth map.
--
--   Let $E$ be a real inner-product space, let $F$ be a real normed space, and let $f:E\to F$ be $C^\infty$. For every $n\in\mathbb N$, $x\in E$, every list of directions $v:\operatorname{Fin}(n)\to E$, and every permutation $\sigma$ of $\operatorname{Fin}(n)$,
--
--   $$D^nf(x)[v\circ\sigma]=D^nf(x)[v].$$
--
--   This provides the higher-order symmetry used when rearranging derivative slots in multilinear and cumulant expansions.
--
--   **Formalization Note.** The smoothness assumption is `ContDiff ℝ ∞`; the statement includes the case $n=0$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IteratedDerivative.lean#L246-L353 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IteratedDerivative`, declaration `FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_comp_perm_of_contDiff`; the repository is private at upload time).

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Symmetry
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_comp_perm_of_contDiff_408915f {f : E → F} (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : E)
    (v : Fin n → E) (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v := by sorry
