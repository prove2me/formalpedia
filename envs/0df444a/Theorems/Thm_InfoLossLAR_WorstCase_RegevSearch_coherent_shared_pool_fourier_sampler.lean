-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_coherent_shared_pool_fourier_sampler
-- name    : InfoLossLAR.WorstCase.RegevSearch.coherent_shared_pool_fourier_sampler
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T02:33:20.150157+00:00
-- url     : https://prove2.me/theorems/23174e03-6b1d-4113-b6b9-4dab17fa850a
-- title:
--   A uniform signed Fourier sampler using coherent shared-pool decoding
-- statement:
--   Given a uniform decoder with the averaged coherent-copy bound and the reduced-basis width schedule, construct a single uniform measured circuit family. For every promised basis, rational target width and unary accuracy, the family must output a valid original-basis signed coefficient prefix almost surely. Its probability on any finite coefficient event must agree to the stated accuracy with the normalized finite Fourier image of the Gaussian. One adequate dyadic grid must work for all events on a given input. The construction must implement the reduced-basis preparation, pool initialization and reuse, the physical coherent decoder calls and uncomputation, the dyadic Fourier circuit and the signed output. Its intrinsic error must be negligible in dimension uniformly over the encoded inputs and accuracies.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, Theorem 3.1 and Lemma 3.14, for the decoding-to-Gaussian reduction. The native circuit and countable common-pool error statements here are specific to this formalization.

import Definitions.Def_InfoLossLAR_RegevSearch_CoherentCopy
import Definitions.Def_InfoLossLAR_RegevSearch_FourierGrid

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch RegevLWE.GaussConv
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch

theorem coherent_shared_pool_fourier_sampler
    (S : Set ℕ) (hS : S.Infinite) (hpos : ∀ n ∈ S, 1 ≤ n)
    (C : MFamily) (hC : IsMQPT C) (P : Polynomial ℕ) (N : ℕ)
    (hcopy : ∀ calls : Polynomial ℕ, ∃ e : ℕ → ℝ,
      Negligible e ∧ SharedPoolCoherence.CopyBudget C P calls N S e)
    (hschedule : ∀ {n : ℕ}, 2 ≤ n →
      ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
      ∀ r : ℚ, 0 < r → dgsThreshold B ≤ (r : ℝ) →
        ∃ D : Matrix (Fin n) (Fin n) ℤ, D.det ≠ 0 ∧ inputModule D = inputModule B ∧
    ∃ W : ℚ, W = max (((n+1 : ℕ) : ℚ) * (1 + ∑ i, ∑ j, |(D i j : ℚ)|)) (r * (famσ n : ℚ)) ∧
    ∃ h : ℕ, h ≤ 5*n+2 ∧
      (∀ j ≤ h, Real.sqrt 2 * (famq n : ℝ) * smoothingParam (inputModule B) (smoothingError n) <
        (W : ℝ) / 2^j) ∧
      Real.sqrt n / (Real.sqrt 2 * (r : ℝ)) ≤ (famσ n : ℝ)/(2*((W : ℝ)/2^h))) :
    ∃ H : MFamily, IsMQPT H ∧ ∃ e : ℕ → ℝ, Negligible e ∧
      ∃ N' : ℕ, ∀ n ∈ S, N' ≤ n →
        ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
        ∀ r : ℚ, 0 < r → dgsThreshold B ≤ (r : ℝ) →
        ∀ k : ℕ, ∃ b : ℕ,
          gridAdequate B (r : ℝ) (2^b) ∧
          outputProb H (dgsInput B r 1 k) (fun out => ∃ z : Fin n → ℤ, encVec encI z <+: out) = 1 ∧
          ∀ T : Finset (Fin n → ℤ),
            |outputProb H (dgsInput B r 1 k) (fun out => ∃ z ∈ T, encVec encI z <+: out) -
              fourierEvent B (r : ℝ) (2^b) T| ≤ e n + 1/(4*((k:ℝ)+1)) := by
  sorry

end InfoLossLAR.WorstCase.RegevSearch
