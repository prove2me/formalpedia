-- Prove2me | Theorems.Thm_NonlinearICAAux_nonlinear_ica_identifiability
-- name    : NonlinearICAAux.nonlinear_ica_identifiability
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:46:47.15323+00:00
-- url     : https://prove2.me/theorems/cd807afa-3b40-4dfa-b148-f696ea96672a
-- title:
--   Theorem 1 (as proved): the contrastive regression recovers the independent components
-- statement:
--   Assume the nonlinear ICA model with auxiliary variables: $\mathbf u\in\mathbb R^m$ has a probability law $\mu$, the sources have conditional density $p(\mathbf s\mid\mathbf u)=\exp\sum_iq_i(s_i,\mathbf u)$, and $\mathbf x=\mathbf f(\mathbf s)$ with $\mathbf f$ a $C^2$ diffeomorphism of $\mathbb R^n$, $\mathbf g=\mathbf f^{-1}$. Assume further:
--
--   1. each $q_i(\cdot,\mathbf u)$ has continuous second derivatives;
--   2. the Assumption of Variability holds;
--   3. $\mathbf h=(h_1,\dots,h_n):\mathbb R^n\to\mathbb R^n$ is invertible, and $\mathbf h$ and $\mathbf h^{-1}$ have continuous second derivatives;
--   4. the regression function of eq. (6) equals the optimal regression function, the log-density ratio of the two classes $\tilde{\mathbf x}=(\mathbf x,\mathbf u)$ and $\tilde{\mathbf x}^*=(\mathbf x,\mathbf u^*)$: for all $\mathbf x$ and $\mathbf u$,
--
--   $$\sum_{i=1}^n\psi_i(h_i(\mathbf x),\mathbf u)=\log p(\mathbf x\mid\mathbf u)-\log p(\mathbf x).$$
--
--   Then the hidden units give the independent components up to a permutation and component-wise invertible transformations: there are a permutation $\sigma$ and bijections $\varphi_i:\mathbb R\to\mathbb R$ with
--
--   $$h_i(\mathbf x)=\varphi_i\big(g_{\sigma(i)}(\mathbf x)\big)=\varphi_i\big(s_{\sigma(i)}\big)\qquad\text{for all }\mathbf x\text{ and }i.$$
--
--   This is the paper's identifiability result for nonlinear ICA with auxiliary variables.
--
--   **Formalization Note** The printed theorem concludes that logistic regression "in the limit of infinite data" with universal approximation is consistent. The proof starts from the identity in item 4, which is what that limit is taken to mean; the passage from the logistic loss to the log-density ratio is the separate statement `logistic_optimum_is_log_ratio`, which holds only almost everywhere. The permutation $\sigma$ is not in the printed conclusion but is produced by the proof and cannot be avoided. Under items 2 and 4 the proof forces $\log p_{\mathbf s}$ to be a sum of functions of single sources, so item 4 can hold only when the sources are marginally independent.
-- source:
--   Hyvärinen, Sasaki and Turner, Nonlinear ICA Using Auxiliary Variables and Generalized Contrastive Learning, arXiv:1805.08651v3 (AISTATS 2019), Section 4.2, Theorem 1, eqs. (4)-(9), pp. 4-5; proof in Supplementary A, p. 11

import Mathlib
import Definitions.Def_NonlinearICAAux_Basic

open MeasureTheory
open scoped ENNReal

namespace NonlinearICAAux

theorem nonlinear_ica_identifiability {n m : ℕ} (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ]
    (q : Fin n → ℝ → (Fin m → ℝ) → ℝ) (f : (Fin n → ℝ) ≃ (Fin n → ℝ))
    (hM : IsAuxICAModel μ q f) (hq : ∀ i u, ContDiff ℝ 2 (fun s => q i s u))
    (hvar : Variability q)
    (h : (Fin n → ℝ) ≃ (Fin n → ℝ)) (hh : IsC2Diffeo h) (ψ : Fin n → ℝ → (Fin m → ℝ) → ℝ)
    (hopt : ∀ x u, regFun ψ h x u = logRatio μ q f x u) :
    ∃ σ : Equiv.Perm (Fin n), ∃ φ : Fin n → ℝ → ℝ, (∀ i, Function.Bijective (φ i)) ∧
      ∀ x i, h x i = φ i (f.symm x (σ i)) := by sorry

end NonlinearICAAux
