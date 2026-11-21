-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dual_parity_width_admissible
-- name    : InfoLossLAR.WorstCase.RegevSketch.dual_parity_width_admissible
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-19T06:23:04.882396+00:00
-- url     : https://prove2.me/theorems/38c80da7-64c9-41dc-96bd-3bbb0bd23251
-- title:
--   Admissibility and smoothing for the determinant-cleared dual
-- statement:
--   In the far regime, the column-doubled lattice remains at least as separated as the original lattice. Its determinant-cleared dual has nonzero determinant and the specified rational width is positive, admissible for DGS and at least twice the smoothing parameter. The dual minimum controls smoothing via the lattice Gaussian packing bound, and the fixed noise scale is $n+2$. The smoothing error is eventually at most $1/8$.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, full version dated May 2, 2009, https://cims.nyu.edu/~regev/papers/qcrypto.pdf. Lemma 3.20 and its preceding reduction from GapSVP to the promise GapCVP variant, full-version PDF p. 30; fixed-family substitution and explicit uniform decision algorithm. Alternative index-two parity and rational covariance specialization of the dual certificate.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
set_option maxHeartbeats 200000
open QAlgorithms.Complexity
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch

theorem dual_parity_width_admissible :
    ∃ C k n₀ : ℕ, 1 ≤ C ∧ ∀ n ≥ n₀, 1 ≤ n →
    ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 → ∀ δ : ℚ, 0 < δ →
    ((C : ℝ) * (famq n : ℝ) * Real.logb 2 ((n : ℝ)+2)^k) * δ < lam1 B →
    let H (i : Fin n) : Matrix (Fin n) (Fin n) ℤ := fun a b => B a b * (if b = i then 2 else 1)
    let D (i : Fin n) := (H i).adjugate.transpose
    let r (i : Fin n) : ℚ := (Int.natAbs (H i).det : ℚ) / (100*δ)
    smoothingError n ≤ 1/8 ∧ ∀ i, (H i).det ≠ 0 ∧ (D i).det ≠ 0 ∧ 0 < r i ∧
      dgsThreshold (D i) ≤ (r i : ℝ) ∧
      RegevLWE.GaussConv.smoothingParam (inputModule (D i)) (smoothingError n) ≤ (r i : ℝ)/2 := by sorry

end InfoLossLAR.WorstCase.RegevSketch
