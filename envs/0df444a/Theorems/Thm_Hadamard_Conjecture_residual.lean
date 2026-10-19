-- Prove2me | Theorems.Thm_Hadamard_Conjecture_residual
-- name    : Hadamard_Conjecture_residual
-- status  : Open
-- author  : @ronr
-- created : 2026-09-05T22:13:21.141903+00:00
-- url     : https://prove2.me/theorems/cd4ba333-e7e7-4976-8259-f5cd3354c8ea
-- title:
--   Hadamard conjecture, residual case after Sylvester and Paley
-- statement:
--   This is the residual case of the Hadamard conjecture left open after removing both the Sylvester family and the Paley-times-power-of-two family.
--
--   For a natural number $k$ satisfying both:
--
--   1. $k$ is **not** a power of two (there is no $m$ with $k = 2^m$), and
--   2. $4k$ is **not** of the form $(q+1) \cdot 2^{t}$ for any prime $q \equiv 3 \pmod 4$ and any natural number $t$,
--
--   the claim is that there still exists a $4k \times 4k$ matrix $M$ with every entry $1$ or $-1$ attaining Hadamard's determinant bound $|\det M| = (4k)^{4k/2}$.
--
--   This is the honest remainder of the conjecture after two classical, unconditionally-proved construction families (`Hadamard_Conjecture_paley_sylvester_case`, itself built from Sylvester's 1867 doubling construction and Paley's 1933 finite-field construction via the Kronecker-product multiplicativity theorem) have been subtracted out. Many further classical constructions exist in the literature (Paley's second construction for $q \equiv 1 \pmod 4$, Williamson matrices, Turyn's construction, and others), each covering additional orders not captured by hypothesis (2) above; none of them, nor any known finite combination, is known to cover every remaining $k$. In particular the first genuinely difficult historical case, order $668 = 4 \times 167$ (resolved only in 2004 by Kharaghani and Tayfeh-Rezaie via a dedicated non-generic construction), lies in this residual family. No proof of this statement for all such $k$ is known; it is exactly as open as the general Hadamard conjecture restricted to this shrinking family.
--
--   **Formalization Note** Matrix entries live in $\mathbb{R}$; membership in $\{1,-1\}$ is expressed as `Finset` membership. The determinant exponent $4k/2$ is a real number via `Real.rpow`.
-- source:
--   Residual case derived from the classical Hadamard conjecture (J. Hadamard, 1893) after removing the case k = 2^m (Sylvester, 1867) and the Paley-times-power-of-two case (R. E. A. C. Paley, 1933, combined with Sylvester via the Kronecker-product multiplicativity theorem). Formal target statement follows the DeepMind formal-conjectures library's determinant form: https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/Hadamard.lean. This further restriction is original to this Prove2Me submission, derived as a refinement of Hadamard_Conjecture_nonpoweroftwo (d44ed3f8-d154-42b6-a6f6-e4e89abcea74) using Hadamard_Conjecture_paley_sylvester_case.

import Mathlib

theorem Hadamard_Conjecture_residual (k : ℕ)
    (hk1 : ¬ ∃ m : ℕ, k = 2 ^ m)
    (hk2 : ¬ ∃ q t : ℕ, Nat.Prime q ∧ q % 4 = 3 ∧ 4 * k = (q + 1) * 2 ^ t) :
    ∃ M : Matrix (Fin (4 * k)) (Fin (4 * k)) ℝ,
      (∀ i j, M i j ∈ ({1, -1} : Finset ℝ)) ∧
      |M.det| = ((4 * k : ℕ) : ℝ) ^ (((4 * k : ℕ) : ℝ) / 2) := by sorry
