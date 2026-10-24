-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_inner_self_apply_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_self_apply_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:05:19.633027+00:00
-- url     : https://prove2.me/theorems/c7c92817-9ac9-4cc2-bd2e-dac043818a48
-- title:
--   Higher Leibniz Rule for an Inner Product Quadratic Form
-- statement:
--   This is the higher-order Leibniz rule for the map $w\mapsto\langle w,G(w)\rangle$.
--
--   Let $E$ be a real inner-product space, let $G:E\to E$ be $C^\infty$, let $d\in\mathbb N$, let $z\in E$, and let $h:\operatorname{Fin}(d+1)\to E$. Then
--
--   $$D^{d+1}\bigl(w\mapsto\langle w,G(w)\rangle\bigr)(z)[h]
--   =\left\langle z,D^{d+1}G(z)[h]\right\rangle
--   +\sum_{k=0}^{d}\left\langle h_k,D^dG(z)[h\text{ with }h_k\text{ removed}]\right\rangle.$$
--
--   The formula is a reusable pointwise identity for differentiating quadratic forms whose first factor is the identity map.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IteratedDerivative.lean#L43-L118 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IteratedDerivative`, declaration `FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_self_apply`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_self_apply_408915f {G : E → E} (hG : ContDiff ℝ ∞ G) (d : ℕ) (z : E)
    (h : Fin (d + 1) → E) :
    iteratedFDeriv ℝ (d + 1) (fun w => ⟪w, G w⟫) z h =
      ⟪z, iteratedFDeriv ℝ (d + 1) G z h⟫ +
        ∑ k : Fin (d + 1), ⟪h k, iteratedFDeriv ℝ d G z (k.removeNth h)⟫ := by sorry
