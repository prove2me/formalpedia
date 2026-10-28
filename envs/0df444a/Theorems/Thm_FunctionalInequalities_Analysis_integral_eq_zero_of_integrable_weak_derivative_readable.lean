-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_eq_zero_of_integrable_weak_derivative_readable
-- name    : FunctionalInequalities.Analysis.integral_eq_zero_of_integrable_weak_derivative_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:05.742215+00:00
-- url     : https://prove2.me/theorems/4bbf5126-d256-459b-9474-606b9a141762
-- title:
--   Integral Of An Integrable Weak Derivative
-- statement:
--   This statement gives the cutoff lemma used for equation (2.1) and Lemma 2.7 of Letwin (arXiv:2607.24164v1).
--
--   Let f and g be real-valued functions on $E=\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin} n)$, and let v∈E. Assume g is a weak directional derivative of f along v, written $\partial_v f=g$, and assume both f and g are integrable with respect to Lebesgue volume. Then
--
--   $$\int_E g(x)\,dx=0.$$
--
--   This is a global zero-mean property for an integrable weak derivative and is reusable as a cutoff argument in weak integration by parts.
--
--   **Formalization Note** No positivity, smoothness, or nonzero-direction assumption is included; the assertion applies to every natural number n and every direction v.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_eq_zero_of_integrable_weak_derivative {n : ℕ}
--       {f g : EuclideanSpace ℝ (Fin n) → ℝ} {v : EuclideanSpace ℝ (Fin n)}
--       (hweak : HasWeakDerivAlong f g v)
--       (hf : Integrable f volume) (hg : Integrable g volume) :
--       (∫ x, g x ∂volume) = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/WeakDerivative/Calculus`](https://prove2.me/theorems/e4287351-4501-4e28-b10c-d6fa6fcca9b5).
--
--   Definition modules: [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Previous: [`integral_compact_flux_eq_neg_forcing_of_global_bounded_weak_test`](https://prove2.me/theorems/68f53a73-98d0-4677-9ebd-c4a0016296fd).
--
--   [Source excerpt, lines 1494–1498](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L1494-L1498) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L1491-L1607 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, declaration `FunctionalInequalities.Analysis.integral_eq_zero_of_integrable_weak_derivative`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus

open MeasureTheory Filter
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.integral_eq_zero_of_integrable_weak_derivative_readable {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} {v : EuclideanSpace ℝ (Fin n)}
    (hweak : HasWeakDerivAlong f g v)
    (hf : Integrable f volume) (hg : Integrable g volume) :
    (∫ x, g x ∂volume) = 0 := by sorry
