-- Prove2me | Theorems.Thm_NonlinearICAAux_order_one_violates_variability
-- name    : NonlinearICAAux.order_one_violates_variability
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:47:10.876036+00:00
-- url     : https://prove2.me/theorems/71735b2d-2f06-45ea-ab92-4d10dd48fc13
-- title:
--   Theorem 2 (i): for conditionally exponential sources of order one the Assumption of Variability fails
-- statement:
--   Assume the nonlinear ICA model with auxiliary variables with $n\ge1$ and each $q_i(\cdot,\mathbf u)$ twice continuously differentiable. If every source $s_i$ is conditionally exponential of order $k=1$ given $\mathbf u$ (Definition 1), that is,
--
--   $$p(s_i\mid\mathbf u)=\frac{Q_i(s_i)}{Z_i(\mathbf u)}\exp\big(\tilde q_{i1}(s_i)\lambda_{i1}(\mathbf u)\big),$$
--
--   then the Assumption of Variability of Theorem 1 does not hold.
--
--   The reason is that, for fixed $\mathbf y$, all differences $\mathbf w(\mathbf y,\mathbf u_j)-\mathbf w(\mathbf y,\mathbf u_0)$ lie in the span of $n$ fixed vectors, while $2n$ independent ones are needed.
--
--   **Formalization Note** The hypothesis $n\ge1$ is implicit in the paper: for $n=0$ the Assumption of Variability asks for an empty family of vectors and holds trivially.
-- source:
--   Hyvärinen, Sasaki and Turner, Nonlinear ICA Using Auxiliary Variables and Generalized Contrastive Learning, arXiv:1805.08651v3 (AISTATS 2019), Section 4.2, Theorem 2, item 1, p. 5; proof in Supplementary B, p. 12

import Mathlib
import Definitions.Def_NonlinearICAAux_Basic

open MeasureTheory
open scoped ENNReal

namespace NonlinearICAAux

theorem order_one_violates_variability {n m : ℕ} (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ]
    (q : Fin n → ℝ → (Fin m → ℝ) → ℝ) (f : (Fin n → ℝ) ≃ (Fin n → ℝ))
    (hM : IsAuxICAModel μ q f) (hq : ∀ i u, ContDiff ℝ 2 (fun s => q i s u)) (hn : 1 ≤ n)
    (hce : ∀ i, IsCondExp q i 1) :
    ¬ Variability q := by sorry

end NonlinearICAAux
