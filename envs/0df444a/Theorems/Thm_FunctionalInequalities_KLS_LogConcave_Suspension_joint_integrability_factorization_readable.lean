-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_joint_integrability_factorization_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.joint_integrability_factorization_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:39.966675+00:00
-- url     : https://prove2.me/theorems/62722319-aff7-42a5-ab4b-17e27bbeed8e
-- title:
--   Factor Integrability and Real Laplace Transform Factorization
-- statement:
--   This lemma states that joint exponential integrability yields integrability of each factor and a real-valued product formula.
--
--   Let $n,N\in\mathbb N$ with $N>0$, $E=\mathbb R^n$ (`EuclideanSpace ℝ (Fin n)`), $\mu$ a probability measure on $E$, and $f:E\to\mathbb R$ measurable. Let $\beta>0$, $\eta_\beta=$ `laplaceMeasure` $\beta$, and $\sigma_\beta=\sqrt{1+2/\beta^2}$ (`sigma`). Put $\lambda=$ `jointLaw` $\mu\ f\ \beta\ \sigma_\beta\ N$, the law of the normalized suspension scalar and the $N$ copies, on $H=$ `JointSpace` $N\ n$. For $z\in H$, write $z_0$ for its scalar coordinate and $z_i\in E$ for its $i$th copy block.
--
--   Assume $p\mapsto e^{\langle z,p\rangle}$ is integrable under $\lambda$. Set $A(s)=e^{(z_0/\sigma_\beta)s}$ and $B_i(x)=e^{\frac{z_0}{\sigma_\beta\sqrt N}f(x)+\langle z_i,x\rangle}$. Then
--   $$
--   A\in L^1(\eta_\beta),\qquad \forall i\in\operatorname{Fin}N,\ B_i\in L^1(\mu),\qquad
--   \int e^{\langle z,p\rangle}\,d\lambda(p)=\left(\int A\,d\eta_\beta\right)\prod_i\int B_i\,d\mu.
--   $$
--
--   This supplies the individual integrability conditions together with the real transform identity. The statement is an implication from joint integrability, not an equivalence.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem joint_integrability_factorization {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
--       [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
--       {β : ℝ} (hβ : 0 < β) (_hN : 0 < N) (z : JointSpace N n)
--       (hInt : Integrable (fun p => Real.exp ⟪z, p⟫) (jointLaw μ f β (sigma β) N)) :
--       Integrable (fun s : ℝ => Real.exp (z none / sigma β * s)) (laplaceMeasure β) ∧
--         (∀ i : Fin N, Integrable (fun x => Real.exp
--           (z none / (sigma β * Real.sqrt N) * f x +
--             ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫)) μ) ∧
--         (∫ p, Real.exp ⟪z, p⟫ ∂jointLaw μ f β (sigma β) N) =
--           (∫ s : ℝ, Real.exp (z none / sigma β * s) ∂laplaceMeasure β) *
--             ∏ i : Fin N, ∫ x, Real.exp
--               (z none / (sigma β * Real.sqrt N) * f x +
--                 ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫) ∂μ
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Suspension/Cumulant`](https://prove2.me/theorems/01ff1334-f332-41dc-ab58-0fb2ead9dd7b).
--
--   Definition modules: [`KLS/BKL/Suspension/Law`](https://prove2.me/theorems/3aa21ca1-97e4-4f56-86c5-3a01d28b38f3), [`Probability/Line/Laplace`](https://prove2.me/theorems/cba52f6e-b244-4595-8333-a1bd8a9b0069).
--
--   Supporting theorems: [`lintegral_exp_inner_jointLaw`](https://prove2.me/theorems/ca4eae99-414a-4309-a1fd-64651f80b00f).
--
--   Previous: [`lintegral_exp_inner_jointLaw`](https://prove2.me/theorems/ca4eae99-414a-4309-a1fd-64651f80b00f) · Next: [`logLaplace_jointLaw_factorization`](https://prove2.me/theorems/d7decbed-2d29-44e0-9116-1fd9deec5adb).
--
--   [Source excerpt, lines 212–224](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Cumulant.lean#L212-L224) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Cumulant.lean#L211-L269 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Cumulant`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.joint_integrability_factorization`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Cumulant

open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace

theorem FunctionalInequalities.KLS.LogConcave.Suspension.joint_integrability_factorization_readable {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β : ℝ} (hβ : 0 < β) (_hN : 0 < N) (z : JointSpace N n)
    (hInt : Integrable (fun p => Real.exp ⟪z, p⟫) (jointLaw μ f β (sigma β) N)) :
    Integrable (fun s : ℝ => Real.exp (z none / sigma β * s)) (laplaceMeasure β) ∧
      (∀ i : Fin N, Integrable (fun x => Real.exp
        (z none / (sigma β * Real.sqrt N) * f x +
          ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫)) μ) ∧
      (∫ p, Real.exp ⟪z, p⟫ ∂jointLaw μ f β (sigma β) N) =
        (∫ s : ℝ, Real.exp (z none / sigma β * s) ∂laplaceMeasure β) *
          ∏ i : Fin N, ∫ x, Real.exp
            (z none / (sigma β * Real.sqrt N) * f x +
              ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫) ∂μ := by sorry
