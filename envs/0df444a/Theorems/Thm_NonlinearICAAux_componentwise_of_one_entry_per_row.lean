-- Prove2me | Theorems.Thm_NonlinearICAAux_componentwise_of_one_entry_per_row
-- name    : NonlinearICAAux.componentwise_of_one_entry_per_row
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:46:06.998039+00:00
-- url     : https://prove2.me/theorems/ccc95a51-554a-4f5e-89f5-2bd1578bde02
-- title:
--   Theorem 1 (proof, last paragraph): one non-zero entry per Jacobian row gives a component-wise map
-- statement:
--   Let $\mathbf v:\mathbb R^n\to\mathbb R^n$ be invertible with $\mathbf v$ and $\mathbf v^{-1}$ both having continuous second derivatives. Suppose that at every $\mathbf y$ no row of the Jacobian of $\mathbf v$ has more than one non-zero entry:
--
--   $$\partial_jv_i(\mathbf y)\,\partial_{j'}v_i(\mathbf y)=0\qquad\text{for all }\mathbf y,\ i,\ j\neq j'.$$
--
--   Then there are a permutation $\sigma$ of $\{1,\dots,n\}$ and bijections $\nu_i:\mathbb R\to\mathbb R$ such that
--
--   $$v_i(\mathbf y)=\nu_i\big(y_{\sigma(i)}\big)\qquad\text{for all }\mathbf y\text{ and }i.$$
--
--   This is the final step of the proof of Theorem 1: by continuity and invertibility of the Jacobian, the non-zero entries stay in the same places for all $\mathbf y$, so each $v_i$ is an invertible function of a single variable.
-- source:
--   Hyvärinen, Sasaki and Turner, Nonlinear ICA Using Auxiliary Variables and Generalized Contrastive Learning, arXiv:1805.08651v3 (AISTATS 2019), Supplementary A, last paragraph, p. 11

import Mathlib
import Definitions.Def_NonlinearICAAux_Basic

open MeasureTheory
open scoped ENNReal

namespace NonlinearICAAux

theorem componentwise_of_one_entry_per_row {n : ℕ} (v : (Fin n → ℝ) ≃ (Fin n → ℝ))
    (hv : IsC2Diffeo v)
    (hrow : ∀ (y : Fin n → ℝ) (i j j' : Fin n), j ≠ j' →
      partialDeriv (fun y => v y i) j y * partialDeriv (fun y => v y i) j' y = 0) :
    ∃ σ : Equiv.Perm (Fin n), ∃ ν : Fin n → ℝ → ℝ, (∀ i, Function.Bijective (ν i)) ∧
      ∀ y i, v y i = ν i (y (σ i)) := by sorry

end NonlinearICAAux
