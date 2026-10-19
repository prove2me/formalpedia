-- Prove2me | Theorems.Thm_Hadamard_Conjecture_paley_primepower_case
-- name    : Hadamard_Conjecture_paley_primepower_case
-- status  : Proved
-- author  : @ronr
-- created : 2026-09-06T00:27:20.325023+00:00
-- url     : https://prove2.me/theorems/9164e8ee-86dc-430e-bac4-73d10cfc4da0
-- title:
--   Hadamard conjecture: Paley over prime-power fields, times a power of two
-- statement:
--   This is the case of the Hadamard conjecture reachable by Paley's constructions over an arbitrary **finite field** (not merely a prime field), combined with Sylvester's doubling construction.
--
--   Let $q = p^{n}$ be a prime power with $n \ge 1$. Suppose $k$ satisfies either
--
--   $$
--   4k = (q+1)\cdot 2^{t} \quad\text{with } q \equiv 3 \pmod 4,
--   \qquad\text{or}\qquad
--   4k = 2(q+1)\cdot 2^{t} \quad\text{with } q \equiv 1 \pmod 4,
--   $$
--
--   for some $t \ge 0$. Then there exists a $4k \times 4k$ matrix $M$ with every entry $1$ or $-1$ attaining Hadamard's determinant bound $|\det M| = (4k)^{4k/2}$.
--
--   **Role.** Paley's constructions (`Paley_construction_I` and `Paley_construction_II`) are stated and proved for an arbitrary finite field of odd characteristic, but the earlier combination theorems on this platform instantiated them only at the prime fields $\mathbb{Z}/q\mathbb{Z}$. Instantiating instead at the Galois field $\mathrm{GF}(p^{n})$ strictly extends the covered orders. Since $n=1$ recovers the prime case, this theorem subsumes both `Hadamard_Conjecture_paley_sylvester_case` and `Hadamard_Conjecture_paley2_sylvester_case`.
--
--   The genuinely new orders come from proper prime powers. For example $q=25$ gives order $2(25+1)=52$, i.e. $k=13$ — and $k=13$ is *not* reachable from any prime via either Paley construction, since none of $51, 25, 12$ (Paley I) nor $25, 12$ (Paley II) is prime. Likewise $q=49$ gives $k=25$, $q=121$ gives $k=61$, $q=169$ gives $k=85$, and $q=343$ gives $k=86$.
--
--   **Formalization Note** The field of order $p^{n}$ is Mathlib's `GaloisField p n`; its `Fintype` instance is obtained from the derived `Finite` instance, and its cardinality from `GaloisField.card` (stated with `Nat.card`). The determinant bound follows internally from the orthogonality identity $MM^{\mathsf T}=4kI_{4k}$.
-- source:
--   R. E. A. C. Paley, On orthogonal matrices, Journal of Mathematics and Physics 12 (1933), 311-320, both constructions, applied over arbitrary finite fields GF(p^n) rather than only prime fields, combined with J. J. Sylvester's 1867 doubling construction via the Kronecker-product multiplicativity theorem. Built on Prove2Me theorems Paley_construction_I (65d083bb-43e4-4dfd-a728-69945984f8e0), Paley_construction_II (087846e2-e39f-4fe7-abfc-c09366c76aa9), and Hadamard_matrix_kronecker_product (635fbe02-d442-43c6-b1a0-b7dff65843e0). Subsumes and strictly extends Hadamard_Conjecture_paley_sylvester_case (f34b2765-011b-466c-995d-499ee3c8daa6) and Hadamard_Conjecture_paley2_sylvester_case (9435d03e-376e-443f-aafb-4a4401eef530).

import Mathlib
open Matrix

theorem Hadamard_Conjecture_paley_primepower_case (k : ℕ)
    (hk : ∃ p n t : ℕ, Nat.Prime p ∧ 0 < n ∧
      ((p ^ n % 4 = 3 ∧ 4 * k = (p ^ n + 1) * 2 ^ t) ∨
       (p ^ n % 4 = 1 ∧ 4 * k = (2 * (p ^ n + 1)) * 2 ^ t))) :
    ∃ M : Matrix (Fin (4 * k)) (Fin (4 * k)) ℝ,
      (∀ i j, M i j ∈ ({1, -1} : Finset ℝ)) ∧
      |M.det| = ((4 * k : ℕ) : ℝ) ^ (((4 * k : ℕ) : ℝ) / 2) := by sorry
