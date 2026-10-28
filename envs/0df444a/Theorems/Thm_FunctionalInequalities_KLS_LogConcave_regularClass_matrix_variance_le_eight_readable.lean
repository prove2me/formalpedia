-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_regularClass_matrix_variance_le_eight_readable
-- name    : FunctionalInequalities.KLS.LogConcave.regularClass_matrix_variance_le_eight_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:54.182297+00:00
-- url     : https://prove2.me/theorems/cfd65a50-1952-469e-9117-ba413e5f75de
-- title:
--   Regular-Class Matrix Variance Bound
-- statement:
--   Let $n>0$, let $K\subset\mathbb R^n$ be compact and convex with nonempty interior, let $\kappa>0$, and let $W:\mathbb R^n\to\mathbb R$ be smooth with $W(y)-\frac\kappa2\|y\|^2$ convex. Let $\mu$ be the normalized isotropic probability measure whose density is $1_Ke^{-W}$ with respect to Lebesgue measure. For every symmetric matrix $M\in\mathbb R^{n\times n}$,
--
--   $$\operatorname{Var}_{\mu}\!\left(x\mapsto\sum_{i,j}M_{ij}x_i x_j\right)
--   \le 8\operatorname{tr}(M^2).$$
--
--   The theorem is the regular-class quadratic variance estimate. The Lean statement quantifies over all symmetric matrices, including singular and indefinite ones.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   include hn hκ hK hKc hKint hW hstrong hμ hiso in
--   set_option maxHeartbeats 1500000 in
--   theorem regularClass_matrix_variance_le_eight :
--       ∀ M : Matrix (Fin n) (Fin n) ℝ, M.IsSymm →
--         variance (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j, M i j*x i*x j)
--           (μ : Measure _) ≤ 8 * Matrix.trace (M*M)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/Letwin/RegularClass`](https://prove2.me/theorems/cc1d2885-a1ae-49de-9545-d4de41532f3e).
--
--   Definition modules: [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02).
--
--   Selected supporting theorems: [`exists_symmetric_isUnit_matrix_sequence`](https://prove2.me/theorems/2457a68a-10fc-4205-94a6-4898596c7fa3), [`integral_fderiv_tilted_eq_integral_mul_fderiv_of_bounded_lipschitz`](https://prove2.me/theorems/80255608-689e-4cd7-80cc-3b2a722fd329), [`symmetric_matrix_spectral_geometry`](https://prove2.me/theorems/a896bf49-4875-4093-8aae-c4e196200010), [`symmetric_trace_integral_extension_mul_of_ae_posSemidef`](https://prove2.me/theorems/bb367c0f-60b7-46e5-bbe8-0f5d9f6169fc), [`gaussianLaw_exp_norm_integrable`](https://prove2.me/theorems/ec40927e-84c2-482a-84b6-84474bc6df0e).
--
--   [Source excerpt, lines 66–71](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/Letwin/RegularClass.lean#L66-L71) · Frozen source `408915f`.
--
--   **Literature**
--
--   This formalizes Theorem 1.2 of Letwin (arXiv:2607.24164v1), cited as “Quadratic-form Poincaré inequality.”
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 1.2. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/Letwin/RegularClass.lean#L66-L148 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.Letwin.RegularClass`, declaration `FunctionalInequalities.KLS.LogConcave.regularClass_matrix_variance_le_eight`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Letwin_RegularClass

open scoped ContDiff
variable {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ Set.univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) =
      (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ)
open MeasureTheory Set Filter ProbabilityTheory
include hn hκ hK hKc hKint hW hstrong hμ hiso
set_option maxHeartbeats 1500000

theorem FunctionalInequalities.KLS.LogConcave.regularClass_matrix_variance_le_eight_readable :
    ∀ M : Matrix (Fin n) (Fin n) ℝ, M.IsSymm →
      variance (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j, M i j*x i*x j)
        (μ : Measure _) ≤ 8 * Matrix.trace (M*M) := by sorry
