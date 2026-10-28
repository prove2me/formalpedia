-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_lintegral_exp_inner_jointLaw_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.lintegral_exp_inner_jointLaw_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:46.328829+00:00
-- url     : https://prove2.me/theorems/ca4eae99-414a-4309-a1fd-64651f80b00f
-- title:
--   Extended Laplace Transform Factorization of the Suspension Joint Law
-- statement:
--   This lemma gives an extended nonnegative Laplace-transform factorization for the suspension joint law.
--
--   Let $n,N\in\mathbb N$, $E=\mathbb R^n$ (`EuclideanSpace ℝ (Fin n)`), and $\mu$ a sigma-finite measure on $E$. Let $f:E\to\mathbb R$ be measurable, and $\beta,\sigma\in\mathbb R$, with $\eta_\beta=$ `laplaceMeasure` $\beta$ sigma-finite. Let $H=$ `JointSpace` $N\ n$, the Euclidean space indexed by $\operatorname{Option}(\operatorname{Fin}N\times\operatorname{Fin}n)$. Write $z_0=z(\mathrm{none})$ and $z_i=(z(\mathrm{some}(i,j)))_j\in E$ for $z\in H$.
--
--   Let $\lambda=$ `jointLaw` $\mu\ f\ \beta\ \sigma\ N$, the pushforward of $\mu^{\otimes N}\otimes\eta_\beta$ by $((x_i),s)\mapsto((N^{-1/2}\sum_i f(x_i)+s)/\sigma,(x_i))$. Then
--   $$
--   \int^-\!\operatorname{ofReal}(e^{\langle z,p\rangle})\,d\lambda(p)
--   =\left(\int^-\!\operatorname{ofReal}(e^{(z_0/\sigma)s})\,d\eta_\beta(s)\right)
--   \prod_{i\in\operatorname{Fin}N}\int^-\!\operatorname{ofReal}\left(e^{\frac{z_0}{\sigma\sqrt N}f(x)+\langle z_i,x\rangle}\right)\,d\mu(x).
--   $$
--
--   This identity is in $[0,\infty]$ (`ENNReal`), with `ENNReal.ofReal` embedding the nonnegative real integrands. It does not require finite integrals, probability measures, $N>0$, or positive $\beta,\sigma$; division uses Lean's totalized real convention.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lintegral_exp_inner_jointLaw {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
--       [SigmaFinite μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) (β σ : ℝ)
--       [SigmaFinite (laplaceMeasure β)] (z : JointSpace N n) :
--       ∫⁻ p, ENNReal.ofReal (Real.exp ⟪z, p⟫) ∂(jointLaw μ f β σ N) =
--         (∫⁻ s, ENNReal.ofReal (Real.exp (z none / σ * s)) ∂laplaceMeasure β) *
--           ∏ i : Fin N, ∫⁻ x, ENNReal.ofReal (Real.exp (z none / (σ * Real.sqrt N) * f x +
--             ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫)) ∂μ
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Suspension/Cumulant`](https://prove2.me/theorems/01ff1334-f332-41dc-ab58-0fb2ead9dd7b).
--
--   Definition modules: [`KLS/BKL/Suspension/Law`](https://prove2.me/theorems/3aa21ca1-97e4-4f56-86c5-3a01d28b38f3), [`Probability/Line/Laplace`](https://prove2.me/theorems/cba52f6e-b244-4595-8333-a1bd8a9b0069).
--
--   Supporting theorems: [`lintegral_pi_prod_fin`](https://prove2.me/theorems/dd8d5725-3056-4089-9664-4a524cef8983).
--
--   Previous: [`sum_sq_cumulant_ge_of_entries`](https://prove2.me/theorems/2c0417e5-0964-49ff-aaed-cde1424459aa) · Next: [`joint_integrability_factorization`](https://prove2.me/theorems/62722319-aff7-42a5-ab4b-17e27bbeed8e).
--
--   [Source excerpt, lines 71–77](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Cumulant.lean#L71-L77) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Cumulant.lean#L69-L189 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Cumulant`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.lintegral_exp_inner_jointLaw`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Cumulant

open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace

theorem FunctionalInequalities.KLS.LogConcave.Suspension.lintegral_exp_inner_jointLaw_readable {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [SigmaFinite μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) (β σ : ℝ)
    [SigmaFinite (laplaceMeasure β)] (z : JointSpace N n) :
    ∫⁻ p, ENNReal.ofReal (Real.exp ⟪z, p⟫) ∂(jointLaw μ f β σ N) =
      (∫⁻ s, ENNReal.ofReal (Real.exp (z none / σ * s)) ∂laplaceMeasure β) *
        ∏ i : Fin N, ∫⁻ x, ENNReal.ofReal (Real.exp (z none / (σ * Real.sqrt N) * f x +
          ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫)) ∂μ := by sorry
