-- Prove2me | Theorems.Thm_HighEntropyLimit_maximally_mixed_expectation_comm
-- name    : HighEntropyLimit.maximally_mixed_expectation_comm
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T21:55:23.105699+00:00
-- url     : https://prove2.me/theorems/d0c54412-c304-4caf-b1fa-3adc6fbf2c8d
-- title:
--   Observables commute in the maximally mixed state
-- statement:
--   Let $n\in\mathbb N$, let $A,B$ be complex $n\times n$ matrices, and let $\rho = I/n$ be the maximally mixed state. Then
--   $$\langle AB\rangle_\rho = \operatorname{tr}(AB\rho) = \operatorname{tr}(BA\rho) = \langle BA\rangle_\rho.$$
-- source:
--   Carcassi, Landini, Aidala, Classical mechanics as the high-entropy limit of quantum mechanics, arXiv:2411.00972v3 (1 Feb 2026), https://arxiv.org/abs/2411.00972, p. 5, Eq. (4)

import Mathlib

namespace HighEntropyLimit
theorem maximally_mixed_expectation_comm (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (A * B * ((n : ℂ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℂ))) =
      Matrix.trace (B * A * ((n : ℂ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℂ))) := by sorry
end HighEntropyLimit
