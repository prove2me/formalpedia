-- Prove2me | Theorems.Thm_KingDiagonal_lieb_thirring_9
-- name    : KingDiagonal.lieb_thirring_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:14:18.544699+00:00
-- url     : https://prove2.me/theorems/294682fb-0a3b-46e5-a0d7-8939bb7b2daa
-- title:
--   Lieb–Thirring inequality (9): $\mathrm{Tr}(VKV^*)^p \le \mathrm{Tr}(V^*V)^{p/2}K^p(V^*V)^{p/2} = \mathrm{Tr}(V^*V)^pK^p$
-- statement:
--   Let $K \ge 0$ be a positive semidefinite $n\times n$ complex matrix and let $V$ be any $k\times n$ complex matrix. Then for every real $p \ge 1$,
--
--   $$
--   \operatorname{Tr}\big(VKV^*\big)^p \;\le\; \operatorname{Tr}(V^*V)^{p/2}\,K^p\,(V^*V)^{p/2} \;=\; \operatorname{Tr}(V^*V)^p K^p .
--   $$
--
--   This is the Lieb–Thirring inequality in the form used by King; the paper cites it (Lieb–Thirring 1976, Araki 1990) and does not prove it. It is the main tool of the proof of Theorem 4, applied to the factorization $(\Phi\otimes\Psi)(\rho) = VKV^*$.
--
--   **Formalization Note** Real matrix powers are given by the continuous functional calculus applied to positive semidefinite matrices. The inequality compares real parts of the (real) traces; the equality is between the complex traces.
--
--   Differences from the source:
--   - encoding: real matrix powers X^p, X^{p/2}, X^{1/2} of positive semidefinite matrices → cfc (fun x : ℝ => x ^ p) X, cfc Real.sqrt X; reason: the continuous functional calculus gives the usual powers on PSD (Hermitian, nonnegative spectrum) matrices, the only inputs used
--   - encoding: inequalities between traces (real numbers) → inequalities between real parts of complex traces; reason: the traces involved are of Hermitian (or products of PSD) matrices and are real; same values
-- source:
--   King, An application of a matrix inequality in quantum information theory, arXiv:quant-ph/0412046v1, eq. (9), p.4

import Mathlib

open scoped Matrix ComplexOrder

namespace KingDiagonal

/-- King, arXiv:quant-ph/0412046v1, eq. (9), p.4 (the Lieb–Thirring inequality, stated in the
paper and cited from [9], [2]; the paper does not prove it): let `K ≥ 0` be a positive
semidefinite `n × n` matrix and `V` any `k × n` matrix. Then for all `p ≥ 1`,
`Tr (V K V*)^p ≤ Tr (V*V)^{p/2} K^p (V*V)^{p/2} = Tr (V*V)^p K^p`.

**Formalization Note.** Real powers of matrices are `cfc (fun x : ℝ => x ^ p)` (`Real.rpow`); every
matrix they are applied to (`V K Vᴴ`, `Vᴴ V`, `K`) is positive semidefinite, so these are the
usual matrix powers. The inequality compares real parts of traces (the traces are real); the
equality is stated for the complex traces themselves. Index sets are arbitrary finite types. -/
theorem lieb_thirring_9 {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    (K : Matrix n n ℂ) (hK : K.PosSemidef) (V : Matrix k n ℂ) (p : ℝ) (hp : 1 ≤ p) :
    (cfc (fun x : ℝ => x ^ p) (V * K * Vᴴ)).trace.re ≤
        (cfc (fun x : ℝ => x ^ (p / 2)) (Vᴴ * V) * cfc (fun x : ℝ => x ^ p) K *
          cfc (fun x : ℝ => x ^ (p / 2)) (Vᴴ * V)).trace.re ∧
      (cfc (fun x : ℝ => x ^ (p / 2)) (Vᴴ * V) * cfc (fun x : ℝ => x ^ p) K *
          cfc (fun x : ℝ => x ^ (p / 2)) (Vᴴ * V)).trace =
        (cfc (fun x : ℝ => x ^ p) (Vᴴ * V) * cfc (fun x : ℝ => x ^ p) K).trace := by sorry

end KingDiagonal
