-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_weightedLaplacian_eq_zero_of_notMem_tsupport_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_eq_zero_of_notMem_tsupport_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:06:27.926192+00:00
-- url     : https://prove2.me/theorems/cee98f37-c875-49b5-aad2-422715a938d1
-- title:
--   Weighted Laplacian Vanishes Outside Closed Support
-- statement:
--   This statement establishes locality of the weighted Laplacian `weightedLaplacian`.
--
--   Let $E$ be a complete finite-dimensional real inner-product space, let $U:E\to\mathbb R$ be arbitrary, let $f:E\to\mathbb R$, and let $x\in E$. If $x$ does not belong to the topological support of $f$, then
--
--   $$
--   \operatorname{weightedLaplacian}(U,f)(x)=0.
--   $$
--
--   The conclusion is independent of the potential $U$ and expresses that the weighted Laplacian vanishes at every point outside the closed support of its argument.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Laplacian.lean#L48-L64 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Laplacian`, declaration `FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_eq_zero_of_notMem_tsupport`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace
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
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_eq_zero_of_notMem_tsupport_408915f (U : E → ℝ) {f : E → ℝ} {x : E}
    (hx : x ∉ tsupport f) : weightedLaplacian U f x = 0 := by sorry
