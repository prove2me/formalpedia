-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_graph_log_integral_hasDerivAt_zero_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.graph_log_integral_hasDerivAt_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:19:34.848604+00:00
-- url     : https://prove2.me/theorems/33019b04-662c-4c4b-b629-8d98f5f8344d
-- title:
--   Derivative of the Graph Logarithmic Integral at Zero
-- statement:
--   This auxiliary lemma identifies a local scalar derivative of a logarithmic exponential integral.
--
--   Let $n\in\mathbb N$, $E=\mathbb R^n$ (`EuclideanSpace ℝ (Fin n)`), $\mu$ a probability measure on $E$, and $f:E\to\mathbb R$ measurable. Let $G(x)=(f(x),x)$ in the Euclidean space indexed by $\operatorname{Option}(\operatorname{Fin}n)$, and put $\Gamma=G_*\mu$ (`Measure.map`). Assume $r>0$ and $y\mapsto e^{r\|y\|}\in L^1(\Gamma)$.
--
--   For every $z\in E$ with $\|z\|<r$, the real function $w\mapsto\log\int e^{wf(x)+\langle z,x\rangle}\,d\mu(x)$ has derivative at $w=0$ equal to the tilted average $F_f(z)$ (`tiltAverage`):
--   $$
--   \left.\frac{d}{dw}\right|_{w=0}\log\left(\int e^{wf(x)+\langle z,x\rangle}\,d\mu(x)\right)
--   =F_f(z),\qquad
--   F_f(z)=\frac{\int e^{\langle z,x\rangle}f(x)\,d\mu(x)}{\int e^{\langle z,x\rangle}\,d\mu(x)}.
--   $$
--
--   The formal conclusion is `HasDerivAt`, so it includes existence of the derivative. This is a local derivative interface under a graph-law exponential norm moment.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem graph_log_integral_hasDerivAt_zero {n : ℕ}
--       (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
--       {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) {r : ℝ} (_hr : 0 < r)
--       (hexp : Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (r * ‖y‖))
--         (μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
--           (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
--             EuclideanSpace ℝ (Option (Fin n))))))
--       (z : EuclideanSpace ℝ (Fin n)) (hz : ‖z‖ < r) :
--       HasDerivAt (fun w : ℝ => Real.log (∫ x, Real.exp (w * f x + ⟪z, x⟫) ∂μ))
--         (tiltAverage μ f z) 0
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Suspension/Derivatives`](https://prove2.me/theorems/3fa39843-9f8d-446f-806f-25b47f8ada2b).
--
--   Definition modules: [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Next: [`joint_first_derivative_of_radii`](https://prove2.me/theorems/36ffa587-610d-4253-bdcc-464589c23e0b).
--
--   [Source excerpt, lines 64–73](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Derivatives.lean#L64-L73) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Derivatives.lean#L63-L160 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Derivatives`, declaration `_private.FunctionalInequalities.KLS.BKL.Suspension.Derivatives.0.FunctionalInequalities.KLS.LogConcave.Suspension.graph_log_integral_hasDerivAt_zero`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Derivatives

open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace

theorem FunctionalInequalities.KLS.LogConcave.Suspension.graph_log_integral_hasDerivAt_zero_readable {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) {r : ℝ} (_hr : 0 < r)
    (hexp : Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (r * ‖y‖))
      (μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
        (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
          EuclideanSpace ℝ (Option (Fin n))))))
    (z : EuclideanSpace ℝ (Fin n)) (hz : ‖z‖ < r) :
    HasDerivAt (fun w : ℝ => Real.log (∫ x, Real.exp (w * f x + ⟪z, x⟫) ∂μ))
      (tiltAverage μ f z) 0 := by sorry
