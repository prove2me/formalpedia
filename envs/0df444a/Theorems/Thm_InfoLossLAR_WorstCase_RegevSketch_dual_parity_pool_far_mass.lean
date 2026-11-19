-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dual_parity_pool_far_mass
-- name    : InfoLossLAR.WorstCase.RegevSketch.dual_parity_pool_far_mass
-- status  : Open
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-18T23:48:51.674318+00:00
-- url     : https://prove2.me/theorems/07718c54-0685-487a-a885-606b38b15ca2
-- title:
--   Far-case admissibility and ideal Gaussian mass for index-two dual certificates
-- statement:
--   Double column i of B, obtaining H. Sample the determinant-cleared dual D=adj(H)^T at width |det H|/(100δ); divide the vectors by det H to obtain dual vectors at width 1/(100δ). In every NO instance beyond an absolute C q log^k gap, the request is admissible: use the dual-minimum smoothing bound, λ₁(Hℤⁿ) ≥ λ₁(Bℤⁿ), scaling, and σ=n+2. Prove that except with probability 1/(16(n+1)), at least a quarter of the samples have odd ith coefficient and the empirical second moment matrix is at most I/(64δ²). The even sector is the index-two sublattice B^{-T}ℤⁿ and the odd sector is its translate: Gaussian coset mass equality up to smoothing error gives odd probability close to one half. The centered lattice Gaussian has subgaussian projections by completing the square; a sphere net and independent-sample concentration control the empirical matrix. The polynomial pool size absorbs both tails. This concerns only an exact product law, not a circuit or decision algorithm.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, full version dated May 2, 2009, https://cims.nyu.edu/~regev/papers/qcrypto.pdf. Lemma 3.20 and its preceding reduction from GapSVP to the promise GapCVP variant, full-version PDF p. 30; fixed-family substitution and explicit uniform decision algorithm. Alternative index-two parity and rational covariance specialization of the dual certificate.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
set_option maxHeartbeats 200000
open QAlgorithms.Complexity
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch

theorem dual_parity_pool_far_mass :
    ∃ C k n₀ : ℕ, 1 ≤ C ∧ ∀ n ≥ n₀, 1 ≤ n →
    ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 → ∀ δ : ℚ, 0 < δ →
    ((C : ℝ) * (famq n : ℝ) * Real.logb 2 ((n : ℝ)+2)^k) * δ < lam1 B →
    let m := (n+1)^3
    let H (i : Fin n) : Matrix (Fin n) (Fin n) ℤ := fun a b => B a b * (if b = i then 2 else 1)
    let D (i : Fin n) := (H i).adjugate.transpose
    let r (i : Fin n) : ℚ := (Int.natAbs (H i).det : ℚ) / (100*δ)
    let E (i : Fin n) (p : Fin m → Fin n → ℤ) : Prop :=
      m ≤ 4 * (Finset.univ.filter (fun j => Odd (p j i))).card ∧
      ∀ x : Fin n → ℤ,
        64 * δ^2 * (∑ j, ((∑ a, x a * ((D i).mulVec (p j)) a : ℤ) : ℚ)^2) ≤
          (m : ℚ) * ((H i).det : ℚ)^2 * (∑ a, (x a : ℚ)^2)
    ∀ i, (D i).det ≠ 0 ∧ 0 < r i ∧ dgsThreshold (D i) ≤ (r i : ℝ) ∧
      1 - 1/(16*((n : ℝ)+1)) ≤ ∑' p : Fin m → Fin n → ℤ,
        (∏ j, coefficientMass (D i) (r i) (p j)) * (@ite ℝ (E i p) (Classical.propDecidable _) 1 0) := by sorry

end InfoLossLAR.WorstCase.RegevSketch
