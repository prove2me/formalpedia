-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_succ_comp_perm_of_fix_zero_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_succ_comp_perm_of_fix_zero_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:04:25.91398+00:00
-- url     : https://prove2.me/theorems/850ee0e8-d161-4c74-8fc2-d3afc427f6bc
-- title:
--   Higher-Derivative Symmetry Under Permutations Fixing One Index
-- statement:
--   This is a technical symmetry lemma for iterated Fréchet derivatives.
--
--   Let $E$ be a real inner-product space, let $F$ be a real normed space, and let $f:E\to F$ be $C^\infty$. Fix $n\in\mathbb N$ and assume that the $n$-th derivative is invariant under every permutation of its $n$ input directions. Then, for every $x\in E$, every $v:\operatorname{Fin}(n+1)\to E$, and every permutation $\sigma$ of $\operatorname{Fin}(n+1)$ satisfying $\sigma(0)=0$,
--
--   $$D^{n+1}f(x)[v\circ\sigma]=D^{n+1}f(x)[v].$$
--
--   The statement supplies the stabilizer-of-the-first-index step in the permutation symmetry of higher derivatives.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IteratedDerivative.lean#L124-L193 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IteratedDerivative`, declaration `FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_succ_comp_perm_of_fix_zero`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_succ_comp_perm_of_fix_zero_408915f {f : E → F} (hf : ContDiff ℝ ∞ f) {n : ℕ}
    (ih : ∀ (y : E) (w : Fin n → E) (τ : Equiv.Perm (Fin n)),
      iteratedFDeriv ℝ n f y (w ∘ τ) = iteratedFDeriv ℝ n f y w)
    (x : E) (v : Fin (n + 1) → E) (σ : Equiv.Perm (Fin (n + 1))) (hσ : σ 0 = 0) :
    iteratedFDeriv ℝ (n + 1) f x (v ∘ σ) = iteratedFDeriv ℝ (n + 1) f x v := by sorry
