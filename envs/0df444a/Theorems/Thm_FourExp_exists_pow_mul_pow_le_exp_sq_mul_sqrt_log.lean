-- Prove2me | Theorems.Thm_FourExp_exists_pow_mul_pow_le_exp_sq_mul_sqrt_log
-- name    : FourExp.exists_pow_mul_pow_le_exp_sq_mul_sqrt_log
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T16:43:55.300463+00:00
-- url     : https://prove2.me/theorems/1cc8c606-255e-418d-a988-71ed7b28748d
-- title:
--   The size estimate at the scale N²/√log N used in the four exponentials construction
-- statement:
--   For all $c, r \in \mathbb{N}$ there is $\kappa > 0$ such that for every $N \ge 3$ and all $S, T, a, b, m$ with
--
--   $$S \le \frac{N^{2}}{\sqrt{\log N}},\quad m \le S,\quad T \le rN,\quad a \le r\,\frac{N}{\sqrt{\log N}},\quad b \le r\,N\sqrt{\log N},$$
--
--   one has
--
--   $$c^{\,c(1+m+S+T(a+b))}\,(1+m+S+T+a+b)^{\,c(1+m+S)} \le e^{\kappa N^{2}\sqrt{\log N}}.$$
--
--   This is the one asymptotic estimate behind the choice of parameters in the four exponentials construction; the grid factor $r$ is $2$ for the linear system and $14$ for the extrapolation.
-- source:
--   The parameter estimates in the proofs of Lemmas 4 and 7 of M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202. Formal proof: Diaz modulus mission, 25 September 2026 (C. Perassi).

import Mathlib

namespace FourExp

/-- The size bound of the four exponentials system in the range of parameters of the proof.

With `s = √(log N) ≥ 1`, take `m ≤ S ≤ N² / s`, `T ≤ r N`, `a ≤ r N / s` and `b ≤ r N s`. Then
`1 + m + S ≤ 3 N² / s`, `T (a + b) ≤ 2 r² N² s` and `1 + m + S + T + a + b ≤ (3 + 3 r) N²`, so the
logarithm of `c^(c (1 + m + S + T (a + b))) · (1 + m + S + T + a + b)^(c (1 + m + S))` is at most
`c (3 + 2 r²) N² s log c + 3 c (N² / s) (log (3 + 3 r) + 2 s²)`, which is `O(N² s)`. -/
theorem exists_pow_mul_pow_le_exp_sq_mul_sqrt_log (c r : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ N S T a b m : ℕ, 3 ≤ N →
      (S : ℝ) ≤ (N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ)) → m ≤ S → T ≤ r * N →
      (a : ℝ) ≤ r * ((N : ℝ) / Real.sqrt (Real.log (N : ℝ))) →
      (b : ℝ) ≤ r * ((N : ℝ) * Real.sqrt (Real.log (N : ℝ))) →
      ((c ^ (c * (1 + m + S + T * (a + b))) * (1 + m + S + T + a + b) ^ (c * (1 + m + S)) : ℕ) : ℝ)
        ≤ Real.exp (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ)))) := by
  sorry

end FourExp
