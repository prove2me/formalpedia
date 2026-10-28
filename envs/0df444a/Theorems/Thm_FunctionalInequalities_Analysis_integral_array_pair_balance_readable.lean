-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_array_pair_balance_readable
-- name    : FunctionalInequalities.Analysis.integral_array_pair_balance_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:49.400497+00:00
-- url     : https://prove2.me/theorems/6a56d72a-b125-4b6e-9809-d8d6e98e7bf3
-- title:
--   Finite Integral Balance for Paired Arrays
-- statement:
--   This is a finite-sum bookkeeping lemma for integrable scalar arrays.
--
--   Let $n\in\mathbb N$, let $A,B,C,D:(\operatorname{Fin} n)^2\times\mathbb R^n\to\mathbb R$, and let $F:\mathbb R^n\to\mathbb R$. Assume that every component of $A,B,C,D$ and $F$ is integrable with respect to Lebesgue measure on `EuclideanSpace ℝ (Fin n)`. Assume also:
--
--   1. For every $a,b\in\operatorname{Fin} n$, the integrals of $A_{ab}+B_{ab}$ and $C_{ab}+D_{ab}$ agree.
--   2. The integral of the finite sum of the $D_{ab}$ equals minus the integral of $F$.
--
--   Then the integral of the finite sum of the $B_{ab}$ equals the negative of the integral of $F-\sum_{a,b}C_{ab}+\sum_{a,b}A_{ab}$:
--
--   $$
--   \int \sum_{a,b}B_{ab}(x)\,dx
--   =-\int\left(F(x)-\sum_{a,b}C_{ab}(x)+\sum_{a,b}A_{ab}(x)\right)dx.
--   $$
--
--   This lemma packages finite summation and linearity of the integral for one subsequent flux identity.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem integral_array_pair_balance {n : ℕ}
--       (A B C D : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
--       (F : EuclideanSpace ℝ (Fin n) → ℝ)
--       (hA : ∀ a b, Integrable (A a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hB : ∀ a b, Integrable (B a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hC : ∀ a b, Integrable (C a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hD : ∀ a b, Integrable (D a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hF : Integrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hPair : ∀ a b,
--         (∫ x, A a b x + B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
--           ∫ x, C a b x + D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hTrace : (∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
--           ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
--         -(∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :
--       (∫ x, ∑ a : Fin n, ∑ b : Fin n, B a b x
--         ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
--       -(∫ x, F x - (∑ a : Fin n, ∑ b : Fin n, C a b x) +
--         ∑ a : Fin n, ∑ b : Fin n, A a b x
--         ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution`](https://prove2.me/theorems/d20d941d-a690-4ebe-9a63-a346adf8dd16).
--
--   Previous: [`localLp_hessian_flux_trace_forcing`](https://prove2.me/theorems/0d14ed2a-5f26-4feb-914f-b0d0e87bf35c) · Next: [`integral_weak_hessian_flux_eq_trace_derivative`](https://prove2.me/theorems/6d0b46f6-29ee-4cf1-8e3f-098cb8c41989).
--
--   [Source excerpt, lines 563–581](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean#L563-L581) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean#L561-L803 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessianEvolution`, declaration `_private.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessianEvolution.0.FunctionalInequalities.Analysis.integral_array_pair_balance`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakHessianEvolution

open MeasureTheory
set_option maxHeartbeats 1200000

theorem FunctionalInequalities.Analysis.integral_array_pair_balance_readable {n : ℕ}
    (A B C D : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hA : ∀ a b, Integrable (A a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hB : ∀ a b, Integrable (B a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hC : ∀ a b, Integrable (C a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hD : ∀ a b, Integrable (D a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hF : Integrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hPair : ∀ a b,
      (∫ x, A a b x + B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, C a b x + D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hTrace : (∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :
    (∫ x, ∑ a : Fin n, ∑ b : Fin n, B a b x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
    -(∫ x, F x - (∑ a : Fin n, ∑ b : Fin n, C a b x) +
      ∑ a : Fin n, ∑ b : Fin n, A a b x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by sorry
