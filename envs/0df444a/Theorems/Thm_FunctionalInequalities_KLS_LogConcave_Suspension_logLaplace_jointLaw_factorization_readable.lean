-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_logLaplace_jointLaw_factorization_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.logLaplace_jointLaw_factorization_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:30.333062+00:00
-- url     : https://prove2.me/theorems/d7decbed-2d29-44e0-9116-1fd9deec5adb
-- title:
--   Logarithmic Laplace Factorization at Integrable Joint Parameters
-- statement:
--   This lemma states the logarithmic Laplace factorization at a parameter with integrable joint exponential.
--
--   Let $n,N\in\mathbb N$ with $N>0$, $E=\mathbb R^n$ (`EuclideanSpace ℝ (Fin n)`), $\mu$ a probability measure on $E$, and $f:E\to\mathbb R$ measurable. Let $\beta>0$, $\eta_\beta=$ `laplaceMeasure` $\beta$, $\sigma_\beta=\sqrt{1+2/\beta^2}$ (`sigma`), and $\lambda=$ `jointLaw` $\mu\ f\ \beta\ \sigma_\beta\ N$. The target $H=$ `JointSpace` $N\ n$ has a scalar coordinate and $N$ copy blocks. For $z\in H$, denote these by $z_0$ and $z_i\in E$.
--
--   Assume $e^{\langle z,\cdot\rangle}\in L^1(\lambda)$. With $\Lambda_\lambda(z)=\log\int e^{\langle z,p\rangle}\,d\lambda(p)$ (`logLaplace`),
--   $$
--   \Lambda_\lambda(z)=
--   \log\left(\int e^{(z_0/\sigma_\beta)s}\,d\eta_\beta(s)\right)
--   +\sum_{i\in\operatorname{Fin}N}\log\left(\int e^{\frac{z_0}{\sigma_\beta\sqrt N}f(x)+\langle z_i,x\rangle}\,d\mu(x)\right).
--   $$
--
--   This gives the real logarithmic identity used in local derivative calculations, with joint integrability explicitly required.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem logLaplace_jointLaw_factorization {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
--       [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
--       {β : ℝ} (hβ : 0 < β) (hN : 0 < N) (z : JointSpace N n)
--       (hInt : Integrable (fun p => Real.exp ⟪z, p⟫) (jointLaw μ f β (sigma β) N)) :
--       FunctionalInequalities.Analysis.BakryEmery.logLaplace (jointLaw μ f β (sigma β) N) z =
--         Real.log (∫ s : ℝ, Real.exp (z none / sigma β * s) ∂laplaceMeasure β) +
--           ∑ i : Fin N, Real.log (∫ x, Real.exp
--             (z none / (sigma β * Real.sqrt N) * f x +
--               ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫) ∂μ)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Suspension/Cumulant`](https://prove2.me/theorems/01ff1334-f332-41dc-ab58-0fb2ead9dd7b).
--
--   Definition modules: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598), [`KLS/BKL/Suspension/Law`](https://prove2.me/theorems/3aa21ca1-97e4-4f56-86c5-3a01d28b38f3), [`Probability/Line/Laplace`](https://prove2.me/theorems/cba52f6e-b244-4595-8333-a1bd8a9b0069).
--
--   Supporting theorems: [`joint_integrability_factorization`](https://prove2.me/theorems/62722319-aff7-42a5-ab4b-17e27bbeed8e).
--
--   Previous: [`joint_integrability_factorization`](https://prove2.me/theorems/62722319-aff7-42a5-ab4b-17e27bbeed8e) · Next: [`exists_f_abs_exponential_moment`](https://prove2.me/theorems/fe683760-0019-4c41-91b0-97d1cf8c50c3).
--
--   [Source excerpt, lines 272–280](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Cumulant.lean#L272-L280) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Cumulant.lean#L271-L294 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Cumulant`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.logLaplace_jointLaw_factorization`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Cumulant

open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace

theorem FunctionalInequalities.KLS.LogConcave.Suspension.logLaplace_jointLaw_factorization_readable {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β : ℝ} (hβ : 0 < β) (hN : 0 < N) (z : JointSpace N n)
    (hInt : Integrable (fun p => Real.exp ⟪z, p⟫) (jointLaw μ f β (sigma β) N)) :
    FunctionalInequalities.Analysis.BakryEmery.logLaplace (jointLaw μ f β (sigma β) N) z =
      Real.log (∫ s : ℝ, Real.exp (z none / sigma β * s) ∂laplaceMeasure β) +
        ∑ i : Fin N, Real.log (∫ x, Real.exp
          (z none / (sigma β * Real.sqrt N) * f x +
            ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫) ∂μ) := by sorry
