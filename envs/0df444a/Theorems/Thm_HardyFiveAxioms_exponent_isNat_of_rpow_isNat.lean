-- Prove2me | Theorems.Thm_HardyFiveAxioms_exponent_isNat_of_rpow_isNat
-- name    : HardyFiveAxioms.exponent_isNat_of_rpow_isNat
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T13:44:47.806258+00:00
-- url     : https://prove2.me/theorems/cfc0b097-0c6b-4331-8eab-3b34e17efd5d
-- title:
--   If every $n^\alpha$ is an integer then $\alpha$ is a positive integer
-- statement:
--   Let $\alpha>0$ be a real number such that $n^\alpha$ is a natural number for every positive integer $n$. Then $\alpha$ is a positive integer:
--
--   $$\alpha\in\{1,2,3,\dots\}.$$
--
--   In Section 8.1 Hardy passes from $K(N)=N^\alpha$ to $K(N)=N^r$ with $r=1,2,3,\dots$ with the words "Since $K$ must be an integer it follows that the power, $\alpha$, must be a positive integer." This milestone isolates that step.
--
--   **Formalization Note** $n^\alpha$ is `Real.rpow` and "is a natural number" means equal to the cast of some `m : ℕ`.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, p. 16, Section 8.1, sentence before Eq. (57)

import Mathlib

namespace HardyFiveAxioms

/-- Hardy 2001, Section 8.1: if `α > 0` and `n^α` is a (natural) integer for every positive
integer `n`, then `α` is a positive integer. -/
theorem exponent_isNat_of_rpow_isNat (α : ℝ) (hα : 0 < α)
    (hint : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, (n : ℝ) ^ α = m) :
    ∃ r : ℕ, 1 ≤ r ∧ α = r := by sorry

end HardyFiveAxioms
