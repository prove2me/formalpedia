-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_iteratedFDeriv_sub_const_of_pos_readable
-- name    : FunctionalInequalities.Analysis.iteratedFDeriv_sub_const_of_pos_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:54.334118+00:00
-- url     : https://prove2.me/theorems/5eae9d29-35ba-4434-ad2d-a584e6ef24b4
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
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem iteratedFDeriv_sub_const_of_pos {f : E → F} (hf : ContDiff ℝ ∞ f) (c : F) {r : ℕ} (hr : 1 ≤ r)
--       (x : E) : iteratedFDeriv ℝ r (fun z => f z - c) x = iteratedFDeriv ℝ r f x
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/IteratedDerivative/GradientJet`](https://prove2.me/theorems/2f9ce587-2ee9-4125-9ef5-333d09ad8523).
--
--   Next: [`inner_iteratedFDeriv_gradient_apply`](https://prove2.me/theorems/98bdd014-ddd3-4c09-a9f1-90cc5a041bc5).
--
--   [Source excerpt, lines 31–32](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/IteratedDerivative/GradientJet.lean#L31-L32) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/IteratedDerivative/GradientJet.lean#L29-L45 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.IteratedDerivative.GradientJet`, declaration `FunctionalInequalities.Analysis.iteratedFDeriv_sub_const_of_pos`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_IteratedDerivative_GradientJet

open scoped RealInnerProductSpace ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem FunctionalInequalities.Analysis.iteratedFDeriv_sub_const_of_pos_readable {f : E → F} (hf : ContDiff ℝ ∞ f) (c : F) {r : ℕ} (hr : 1 ≤ r)
    (x : E) : iteratedFDeriv ℝ r (fun z => f z - c) x = iteratedFDeriv ℝ r f x := by sorry
