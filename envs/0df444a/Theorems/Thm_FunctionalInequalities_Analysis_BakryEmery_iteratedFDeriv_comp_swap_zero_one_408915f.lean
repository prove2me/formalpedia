-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_comp_swap_zero_one_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_comp_swap_zero_one_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:04:26.634822+00:00
-- url     : https://prove2.me/theorems/20d8822f-4aa8-43e8-9b6e-9732bc8a8e63
-- title:
--   Swap Symmetry of Higher Derivatives
-- statement:
--   This is a pointwise Schwarz-type symmetry statement for iterated Fréchet derivatives.
--
--   Let $E$ be a real inner-product space, let $F$ be a real normed space, and let $f:E\to F$ be $C^\infty$. For every $n\in\mathbb N$, $x\in E$, and $v:\operatorname{Fin}(n+2)\to E$, swapping the first two derivative directions leaves the $(n+2)$-nd iterated derivative unchanged:
--
--   $$D^{n+2}f(x)[v\circ(0\ 1)]=D^{n+2}f(x)[v].$$
--
--   Here $(0\ 1)$ is the permutation exchanging the indices $0$ and $1$.
--
--   The lemma is a technical component for establishing full permutation symmetry of higher derivatives.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IteratedDerivative.lean#L220-L244 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IteratedDerivative`, declaration `FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_comp_swap_zero_one`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_comp_swap_zero_one_408915f {f : E → F} (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : E)
    (v : Fin (n + 2) → E) :
    iteratedFDeriv ℝ (n + 2) f x (v ∘ Equiv.swap 0 1) = iteratedFDeriv ℝ (n + 2) f x v := by sorry
