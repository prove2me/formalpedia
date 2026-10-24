-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_iteratedFDeriv_sub_const_of_pos_408915f
-- name    : FunctionalInequalities.Analysis.iteratedFDeriv_sub_const_of_pos_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:03:38.10099+00:00
-- url     : https://prove2.me/theorems/b2034f3e-3769-4164-bcbe-8a97a864c19f
-- title:
--   Higher Derivative Invariance Under Constant Shifts
-- statement:
--   This is the shift invariance of positive-order iterated derivatives.
--
--   Let $E$ and $F$ be real normed spaces, let $f:E\to F$ be smooth, let $c\in F$, let $r\in\mathbb N$ satisfy $r\geq1$, and let $x\in E$. Then
--
--   $$
--   D^r(f-c)(x)=D^rf(x).
--   $$
--
--   Here $f-c$ denotes the function $z\mapsto f(z)-c$. The conclusion is stated using `iteratedFDeriv`; no inner-product, completeness, finite-dimensionality, or measure assumptions are required.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/IteratedDerivative/GradientJet.lean#L29-L45 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.IteratedDerivative.GradientJet`, declaration `FunctionalInequalities.Analysis.iteratedFDeriv_sub_const_of_pos`; the repository is private at upload time).

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

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
section Shift
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem FunctionalInequalities.Analysis.iteratedFDeriv_sub_const_of_pos_408915f {f : E → F} (hf : ContDiff ℝ ∞ f) (c : F) {r : ℕ} (hr : 1 ≤ r)
    (x : E) : iteratedFDeriv ℝ r (fun z => f z - c) x = iteratedFDeriv ℝ r f x := by sorry
