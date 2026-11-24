-- Prove2me | Theorems.Thm_NonlinearICAAux_jacobian_cross_terms_vanish
-- name    : NonlinearICAAux.jacobian_cross_terms_vanish
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:45:35.800124+00:00
-- url     : https://prove2.me/theorems/1dd7b58a-0b84-4371-b3f6-7ab39d6a37d5
-- title:
--   Theorem 1 (proof, eqs. (17)-(27)): the Assumption of Variability forces $\mathbf M(\mathbf y)=0$
-- statement:
--   Let $q_1,\dots,q_n$ be such that each $q_i(\cdot,\mathbf u)$ has continuous second derivatives and the Assumption of Variability holds. Let $\mathbf v:\mathbb R^n\to\mathbb R^n$ have continuous second derivatives, and suppose there are functions $\psi_i$ and $\bar q$ such that, for all $\mathbf y\in\mathbb R^n$ and all $\mathbf u$ (eq. (17)),
--
--   $$\sum_{i=1}^n\psi_i(y_i,\mathbf u)=\sum_{i=1}^n q_i(v_i(\mathbf y),\mathbf u)-\bar q(\mathbf y).$$
--
--   Then for every $\mathbf y$, every $i$ and every $j\neq j'$,
--
--   $$\partial_jv_i(\mathbf y)\,\partial_{j'}v_i(\mathbf y)=0\qquad\text{and}\qquad\partial_{j'}\partial_jv_i(\mathbf y)=0,$$
--
--   that is, the matrix $\mathbf M(\mathbf y)$ of eq. (23) vanishes.
--
--   In the proof of Theorem 1, $\mathbf v=\mathbf g\circ\mathbf h^{-1}$ and $\bar q=\log p_{\mathbf s}\circ\mathbf v$; the conclusion says that no row of the Jacobian of $\mathbf v$ has two non-zero entries.
--
--   **Formalization Note** No regularity is assumed of $\psi_i$ or $\bar q$. The paper differentiates $\bar q=\log p_{\mathbf s}\circ\mathbf v$ twice, which its assumptions do not justify; the statement is the one obtained by first subtracting eq. (17) at $\mathbf u_0$, as the paper does in eq. (27), which removes $\bar q$ and $\psi$ from the differentiated identity.
-- source:
--   Hyvärinen, Sasaki and Turner, Nonlinear ICA Using Auxiliary Variables and Generalized Contrastive Learning, arXiv:1805.08651v3 (AISTATS 2019), Supplementary A, eqs. (17)-(27) and the paragraph after (27), p. 11

import Mathlib
import Definitions.Def_NonlinearICAAux_Basic

open MeasureTheory
open scoped ENNReal

namespace NonlinearICAAux

theorem jacobian_cross_terms_vanish {n m : ℕ} (q : Fin n → ℝ → (Fin m → ℝ) → ℝ)
    (hq : ∀ i u, ContDiff ℝ 2 (fun s => q i s u)) (hvar : Variability q)
    (v : (Fin n → ℝ) → (Fin n → ℝ)) (hv : ContDiff ℝ 2 v)
    (ψ : Fin n → ℝ → (Fin m → ℝ) → ℝ) (qbar : (Fin n → ℝ) → ℝ)
    (h17 : ∀ y u, ∑ i, ψ i (y i) u = ∑ i, q i (v y i) u - qbar y) :
    ∀ (y : Fin n → ℝ) (i j j' : Fin n), j ≠ j' →
      partialDeriv (fun y => v y i) j y * partialDeriv (fun y => v y i) j' y = 0 ∧
      partialDeriv (fun y' => partialDeriv (fun y => v y i) j y') j' y = 0 := by sorry

end NonlinearICAAux
