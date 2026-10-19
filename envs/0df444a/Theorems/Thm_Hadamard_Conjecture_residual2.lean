-- Prove2me | Theorems.Thm_Hadamard_Conjecture_residual2
-- name    : Hadamard_Conjecture_residual2
-- status  : Open
-- author  : @ronr
-- created : 2026-09-06T00:02:16.699973+00:00
-- url     : https://prove2.me/theorems/ee0d93a1-ab6e-46f3-a51b-4f300f86a291
-- title:
--   Hadamard conjecture, residual case after Sylvester, Paley I, and Paley II
-- statement:
--   This is the residual case of the Hadamard conjecture left open after removing the Sylvester family, the Paley-I-times-power-of-two family, and the Paley-II-times-power-of-two family.
--
--   For a natural number $k$ satisfying all three of:
--
--   1. $k$ is **not** a power of two,
--   2. $4k$ is **not** of the form $(q+1)\cdot2^{t}$ for a prime $q\equiv3\pmod4$, and
--   3. $4k$ is **not** of the form $2(q+1)\cdot2^{t}$ for a prime $q\equiv1\pmod4$,
--
--   the claim is that there still exists a $4k\times4k$ matrix $M$ with every entry $1$ or $-1$ attaining Hadamard's determinant bound $|\det M|=(4k)^{4k/2}$.
--
--   This is the honest remainder of the conjecture after three classical, unconditionally-proved construction families (`Hadamard_Conjecture_paley_sylvester_case` from Paley's first construction, and `Hadamard_Conjecture_paley2_sylvester_case` from Paley's second construction, each combined with Sylvester's doubling construction via the Kronecker-product multiplicativity theorem) have been subtracted out. Further classical constructions exist in the literature (Williamson matrices, Turyn's construction, Baumert-Hall arrays, and others) that would shrink this residual further, but none of them, nor any known finite combination, is known to cover every remaining $k$. In particular the first genuinely difficult historical case, order $668=4\times167$ (resolved only in 2004 by Kharaghani and Tayfeh-Rezaie via a dedicated non-generic construction), lies in this residual family. No proof of this statement for all such $k$ is known; it is exactly as open as the general Hadamard conjecture restricted to this shrinking family.
--
--   **Formalization Note** Matrix entries live in $\mathbb{R}$; membership in $\{1,-1\}$ is expressed as `Finset` membership. The determinant exponent $4k/2$ is a real number via `Real.rpow`.
-- source:
--   Residual case derived from the classical Hadamard conjecture (J. Hadamard, 1893) after removing the case k = 2^m (Sylvester, 1867), the Paley-I-times-power-of-two case (Paley 1933, q = 3 mod 4, combined with Sylvester), and the Paley-II-times-power-of-two case (Paley 1933, q = 1 mod 4, combined with Sylvester). Formal target statement follows the DeepMind formal-conjectures library's determinant form: https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/Hadamard.lean. This further restriction is original to this Prove2Me submission, derived as a refinement of Hadamard_Conjecture_residual (cd4ba333-e7e7-4976-8259-f5cd3354c8ea) using Hadamard_Conjecture_paley2_sylvester_case.

import Mathlib

theorem Hadamard_Conjecture_residual2 (k : ℕ)
    (hk1 : ¬ ∃ m : ℕ, k = 2 ^ m)
    (hk2 : ¬ ∃ q t : ℕ, Nat.Prime q ∧ q % 4 = 3 ∧ 4 * k = (q + 1) * 2 ^ t)
    (hk3 : ¬ ∃ q t : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ 4 * k = (2 * (q + 1)) * 2 ^ t) :
    ∃ M : Matrix (Fin (4 * k)) (Fin (4 * k)) ℝ,
      (∀ i j, M i j ∈ ({1, -1} : Finset ℝ)) ∧
      |M.det| = ((4 * k : ℕ) : ℝ) ^ (((4 * k : ℕ) : ℝ) / 2) := by sorry
