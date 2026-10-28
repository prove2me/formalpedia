-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_Euclidean_norm_mul_fderiv_comp_sub_smul_le_readable
-- name    : FunctionalInequalities.Energy.Euclidean.norm_mul_fderiv_comp_sub_smul_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:15.201466+00:00
-- url     : https://prove2.me/theorems/ac853596-8eb4-4516-8eb3-374b5c046e01
-- title:
--   Derivative Domination Near a Translated Point
-- statement:
--   This is a pointwise domination estimate for translated directional derivatives.
--
--   Let $V$ be a real inner-product space, let $\phi:V\to\mathbb R$, let $M\in\mathbb R$, let $h:V\to\mathbb R$, let $v\in V$, and let $s,t\in\mathbb R$ satisfy
--
--   $$
--   |s-t|<1.
--   $$
--
--   Assume that the Fréchet derivative of $\phi$ is uniformly bounded:
--
--   $$
--   \|D\phi(y)\|\le M\qquad\text{for every }y\in V.
--   $$
--
--   Then for every $x\in V$,
--
--   $$
--   \left\|h(x)D\phi(x-sv)v\right\|
--   \le
--   \mathbf 1_{\operatorname{cthickening}((|t|+1)\|v\|,\operatorname{tsupport}(\phi))}(x)
--   \,|h(x)|M\|v\|.
--   $$
--
--   The estimate localizes the translated derivative to a thickening of the topological support of $\phi$ and is used for dominated differentiation under an integral.
--
--   **Formalization Note** The right-hand side is a set indicator; outside the thickening the derivative is forced to vanish by the support condition.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.Euclidean`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_mul_fderiv_comp_sub_smul_le {φ : V → ℝ} {M : ℝ}
--       (hM : ∀ y, ‖fderiv ℝ φ y‖ ≤ M) (h : V → ℝ) (v : V) {t s : ℝ} (hs : dist s t < 1) (x : V) :
--       ‖h x * fderiv ℝ φ (x - s • v) v‖ ≤
--         (Metric.cthickening ((|t| + 1) * ‖v‖) (tsupport φ)).indicator
--           (fun y => |h y| * (M * ‖v‖)) x
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Euclidean/ZeroGradient`](https://prove2.me/theorems/52f28c92-8879-4a35-be78-f95c88a2a467).
--
--   Next: [`hasDerivAt_integral_mul_translate`](https://prove2.me/theorems/578ccf2b-12bc-48b1-889e-1bee05d7af56).
--
--   [Source excerpt, lines 40–44](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Euclidean/ZeroGradient.lean#L40-L44) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/ZeroGradient.lean#L38-L81 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.ZeroGradient`, declaration `FunctionalInequalities.Energy.Euclidean.norm_mul_fderiv_comp_sub_smul_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_ZeroGradient

universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem FunctionalInequalities.Energy.Euclidean.norm_mul_fderiv_comp_sub_smul_le_readable {φ : V → ℝ} {M : ℝ}
    (hM : ∀ y, ‖fderiv ℝ φ y‖ ≤ M) (h : V → ℝ) (v : V) {t s : ℝ} (hs : dist s t < 1) (x : V) :
    ‖h x * fderiv ℝ φ (x - s • v) v‖ ≤
      (Metric.cthickening ((|t| + 1) * ‖v‖) (tsupport φ)).indicator
        (fun y => |h y| * (M * ‖v‖)) x := by sorry
