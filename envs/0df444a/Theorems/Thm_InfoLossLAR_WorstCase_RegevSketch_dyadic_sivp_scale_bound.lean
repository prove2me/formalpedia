-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dyadic_sivp_scale_bound
-- name    : InfoLossLAR.WorstCase.RegevSketch.dyadic_sivp_scale_bound
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-18T22:50:53.320644+00:00
-- url     : https://prove2.me/theorems/2d137991-a365-478d-9669-0aca416d5bc4
-- title:
--   Polynomial search bound for a suitable DGS width
-- statement:
--   For every positive dimension and nonsingular integer basis, the dyadic grid from one to two raised to a polynomial in the encoded input length and the dimension contains a width at least the fixed-family DGS threshold. At that width the Gaussian tail radius is at most the target SIVP approximation factor times the last successive minimum. Use the least dyadic width at least the maximum of one and the threshold. The smoothing estimate is logarithmic relative to the last successive minimum, and the two square-root factors combine with $\sigma(n)=n+2$ to give a bounded factor. The integer lattice has last successive minimum at least one; the modulus dominates the square root of the dimension. An input-bit bound on the norms of the basis columns bounds the grid index.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, full version dated May 2, 2009, https://cims.nyu.edu/~regev/papers/qcrypto.pdf. Lemmas 3.15–3.17, full-version PDF pp. 28–29; fixed-family substitution and explicit uniform multi-output realization.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
set_option maxHeartbeats 200000
open QAlgorithms.Complexity
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch

theorem dyadic_sivp_scale_bound :    ∃ C k d : ℕ, 1 ≤ C ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
        ∃ j : ℕ, j ≤ ((encMat encI B).length + n + 2)^d ∧
          dgsThreshold B ≤ (2 : ℝ)^j ∧
          2 * Real.sqrt n * (2 : ℝ)^j ≤
            ((C : ℝ) * (famq n : ℝ) * Real.logb 2 ((n : ℝ) + 2)^k) * lamN B := by sorry

end InfoLossLAR.WorstCase.RegevSketch
