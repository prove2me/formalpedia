-- Prove2me | Theorems.Thm_NonlinearICAAux_logistic_optimum_is_log_ratio
-- name    : NonlinearICAAux.logistic_optimum_is_log_ratio
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:44:37.496452+00:00
-- url     : https://prove2.me/theorems/396f74d4-98bc-4513-8acf-9f1b78610271
-- title:
--   Theorem 1 (proof, first step): the population logistic-regression optimum is the log-density ratio
-- statement:
--   Assume the nonlinear ICA model with auxiliary variables (eqs. (1), (4)), and let $\tilde{\mathbf x}=(\mathbf x,\mathbf u)$ and $\tilde{\mathbf x}^*=(\mathbf x,\mathbf u^*)$, with $\mathbf u^*$ an independent copy of $\mathbf u$, be the two classes of eq. (5). For a measurable regression function $r(\mathbf x,\mathbf u)$ let
--
--   $$J(r)=\mathbb E_{\tilde{\mathbf x}}\log\big(1+e^{-r(\mathbf x,\mathbf u)}\big)+\mathbb E_{\tilde{\mathbf x}^*}\log\big(1+e^{r(\mathbf x,\mathbf u^*)}\big)\in[0,\infty]$$
--
--   be the population logistic loss with equal class weights. Then the log-density ratio $r^*(\mathbf x,\mathbf u)=\log p(\mathbf x\mid\mathbf u)-\log p(\mathbf x)$ is measurable and minimises $J$ over all measurable $r$, and every measurable minimiser of $J$ equals $r^*$ almost everywhere with respect to Lebesgue measure times the law of $\mathbf u$.
--
--   This is the "well-known theory" invoked in the first line of the proof of Theorem 1: logistic regression with infinite data and unrestricted function class converges to the difference of the log-densities of the two classes.
--
--   **Formalization Note** The paper cites this fact (Gutmann and Hyvärinen, 2012) without proof. The two expectations are integrals against the densities $p(\mathbf x\mid\mathbf u)$ and $p(\mathbf x)$ with respect to Lebesgue measure times the law of $\mathbf u$.
-- source:
--   Hyvärinen, Sasaki and Turner, Nonlinear ICA Using Auxiliary Variables and Generalized Contrastive Learning, arXiv:1805.08651v3 (AISTATS 2019), Section 3.2, eqs. (5)-(6), p. 3; Supplementary A, first display before eq. (17), p. 11

import Mathlib
import Definitions.Def_NonlinearICAAux_Basic

open MeasureTheory
open scoped ENNReal

namespace NonlinearICAAux

theorem logistic_optimum_is_log_ratio {n m : ℕ} (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ]
    (q : Fin n → ℝ → (Fin m → ℝ) → ℝ) (f : (Fin n → ℝ) ≃ (Fin n → ℝ))
    (hM : IsAuxICAModel μ q f) :
    Measurable (fun p : (Fin n → ℝ) × (Fin m → ℝ) => logRatio μ q f p.1 p.2) ∧
    (∀ r : (Fin n → ℝ) × (Fin m → ℝ) → ℝ, Measurable r →
      logisticLoss μ q f (fun p => logRatio μ q f p.1 p.2) ≤ logisticLoss μ q f r) ∧
    (∀ r : (Fin n → ℝ) × (Fin m → ℝ) → ℝ, Measurable r →
      (∀ r' : (Fin n → ℝ) × (Fin m → ℝ) → ℝ, Measurable r' →
        logisticLoss μ q f r ≤ logisticLoss μ q f r') →
      r =ᵐ[(volume : Measure (Fin n → ℝ)).prod μ] fun p => logRatio μ q f p.1 p.2) := by sorry

end NonlinearICAAux
