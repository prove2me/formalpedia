-- Prove2me | Theorems.Thm_NonlinearICAAux_conditionally_exponential_linear_indeterminacy
-- name    : NonlinearICAAux.conditionally_exponential_linear_indeterminacy
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:48:08.445538+00:00
-- url     : https://prove2.me/theorems/de836b2d-7a7c-4e95-8474-4faa89ab7af8
-- title:
--   Theorem 3 (as proved): conditionally exponential sources are recovered up to a linear transformation of their sufficient statistics
-- statement:
--   Assume the nonlinear ICA model with auxiliary variables, and that every source $s_i$ is conditionally exponential of order $k$ given $\mathbf u$ (Definition 1):
--
--   $$p(s_i\mid\mathbf u)=\frac{Q_i(s_i)}{Z_i(\mathbf u)}\exp\sum_{j=1}^k\tilde q_{ij}(s_i)\lambda_{ij}(\mathbf u).$$
--
--   Assume there are $nk+1$ points $\mathbf u_0,\dots,\mathbf u_{nk}$ for which the $nk\times nk$ matrix $\bar{\mathbf L}$ with entries $\lambda_{ij}(\mathbf u_l)-\lambda_{ij}(\mathbf u_0)$ (row $(i,j)$, column $l$) is invertible (eq. (10)). Then:
--
--   1. the optimal regression function, the log-density ratio, can be written as
--   $$\log p(\mathbf x\mid\mathbf u)-\log p(\mathbf x)=\tilde{\mathbf h}(\mathbf x)^T\mathbf v(\mathbf u)+a(\mathbf x)+b(\mathbf u)$$
--   for some $\tilde{\mathbf h}:\mathbb R^n\to\mathbb R^{nk}$, $\mathbf v:\mathbb R^m\to\mathbb R^{nk}$ and scalar functions $a,b$ (eq. (11));
--   2. whenever a regression function of the form (11) equals the log-density ratio for all $\mathbf x$ and $\mathbf u$, there are a matrix $\mathbf A$ and a vector $\mathbf c$ such that, with $\mathbf s=\mathbf g(\mathbf x)$,
--   $$\big(\tilde q_{11}(s_1),\tilde q_{12}(s_1),\dots,\tilde q_{nk}(s_n)\big)^T=\mathbf A\,\tilde{\mathbf h}(\mathbf x)-\mathbf c\qquad\text{for all }\mathbf x\quad\text{(eq. (12))}.$$
--
--   So, as in time-contrastive learning, the hidden units recover the sufficient statistics of the sources only up to a linear transformation.
--
--   **Formalization Note** The printed Assumption 4 refers to the regression function of eq. (6), but the proof and the conclusion use the form (11); the statement uses (11). "In the limit of infinite data" is encoded, as for Theorem 1, as equality with the log-density ratio. The matrix $\mathbf A$ is not claimed to be invertible, as in the paper.
-- source:
--   Hyvärinen, Sasaki and Turner, Nonlinear ICA Using Auxiliary Variables and Generalized Contrastive Learning, arXiv:1805.08651v3 (AISTATS 2019), Section 4.3, Theorem 3, eqs. (10)-(12), pp. 5-6; proof in Supplementary C, eqs. (32)-(40), p. 12

import Mathlib
import Definitions.Def_NonlinearICAAux_Basic

open MeasureTheory
open scoped ENNReal

namespace NonlinearICAAux

theorem conditionally_exponential_linear_indeterminacy {n m k : ℕ} (μ : Measure (Fin m → ℝ))
    [IsProbabilityMeasure μ] (q : Fin n → ℝ → (Fin m → ℝ) → ℝ) (f : (Fin n → ℝ) ≃ (Fin n → ℝ))
    (hM : IsAuxICAModel μ q f)
    (Q : Fin n → ℝ → ℝ) (Z : Fin n → (Fin m → ℝ) → ℝ) (qt : Fin n → Fin k → ℝ → ℝ)
    (lam : Fin n → Fin k → (Fin m → ℝ) → ℝ)
    (hce : ∀ i, IsCondExpWith q i (Q i) (Z i) (qt i) (lam i))
    (hL : ∃ (u₀ : Fin m → ℝ) (us : Fin n × Fin k → (Fin m → ℝ)), IsUnit (lamBar lam u₀ us)) :
    (∃ (ht : (Fin n → ℝ) → (Fin n × Fin k → ℝ)) (v : (Fin m → ℝ) → (Fin n × Fin k → ℝ))
        (a : (Fin n → ℝ) → ℝ) (b : (Fin m → ℝ) → ℝ),
        ∀ x u, logRatio μ q f x u = regExp ht v a b x u) ∧
    (∀ (ht : (Fin n → ℝ) → (Fin n × Fin k → ℝ)) (v : (Fin m → ℝ) → (Fin n × Fin k → ℝ))
        (a : (Fin n → ℝ) → ℝ) (b : (Fin m → ℝ) → ℝ),
        (∀ x u, regExp ht v a b x u = logRatio μ q f x u) →
        ∃ (A : Matrix (Fin n × Fin k) (Fin n × Fin k) ℝ) (c : Fin n × Fin k → ℝ),
          ∀ x, sstatVec qt (f.symm x) = A.mulVec (ht x) - c) := by sorry

end NonlinearICAAux
