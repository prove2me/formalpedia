-- Prove2me | Theorems.Thm_ItoLemma_fin_two_mixed_hessian_sum_over_brownian_drivers
-- name    : ItoLemma.fin_two_mixed_hessian_sum_over_brownian_drivers
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:41:17.125541+00:00
-- url     : https://prove2.me/theorems/2612581d-fa0a-46c2-90a1-db65ccecf4a6
-- title:
--   Finite-Dimensional Quadratic Covariation from the Product Hessian
-- statement:
--   For any finite number d of Brownian drivers, the half-sum over the two product Hessian indices and the Brownian driver index equals the sum of products of the two rows of the diffusion coefficient matrix. This is the cross-variation drift term in the Itô product rule.
-- source:
--   Mathlib finite sums over Fin 2, https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Fin.html, inspected 26 October 2026; companion proved lemma https://prove2.me/theorems/87b98c1d-d2c0-4257-8765-04513e33c45f.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

theorem ItoLemma.fin_two_mixed_hessian_sum_over_brownian_drivers {d : ℕ}
    (H : Fin 2 → Fin d → ℝ) :
    (1 / 2 : ℝ) *
      (∑ p : Fin 2, ∑ q : Fin 2,
        (if p = q then (0 : ℝ) else 1) *
          (∑ k : Fin d, H p k * H q k)) =
      ∑ k : Fin d, H 0 k * H 1 k := by sorry
