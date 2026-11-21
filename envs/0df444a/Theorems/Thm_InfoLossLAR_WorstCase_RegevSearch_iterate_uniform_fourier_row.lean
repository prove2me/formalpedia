-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_iterate_uniform_fourier_row
-- name    : InfoLossLAR.WorstCase.RegevSearch.iterate_uniform_fourier_row
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T05:31:30.877177+00:00
-- url     : https://prove2.me/theorems/e9eca0d1-f13b-4c59-b794-d0787a28e2b7
-- title:
--   Iteration of a uniform shared-pool Fourier sampler
-- statement:
--   A uniform one-step Fourier sampler and the coherent copy budget give a single uniform quantum circuit family at the requested Gaussian width. The family loads an initial wide Gaussian pool, applies the width schedule on disjoint fresh registers while retaining the old pool, and makes a final one-row readout. Its law on finite events differs from the finite-grid Fourier law by a negligible term plus the requested inverse-precision allowance.
-- source:
--   InfoLossLAR formalization of the single-coefficient Gaussian reduction, coherent shared-pool Fourier sampling, https://prove2.me/theorems/23174e03-6b1d-4113-b6b9-4dab17fa850a

import Definitions.Def_InfoLossLAR_RegevSearch_UniformFourierRow

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open InfoLossLAR.WorstCase.RegevSearch.GaussianIteration
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch

theorem iterate_uniform_fourier_row (S : Set ℕ) (C : MFamily) (P : Polynomial ℕ) (N : ℕ)
    (hcopy : ∀ calls : Polynomial ℕ, ∃ e : ℕ→ℝ, Negligible e ∧ SharedPoolCoherence.CopyBudget C P calls N S e)
    (row : UniformFourierRow C P) :
    ∃ H : MFamily, IsMQPT H ∧ ∃ e : ℕ→ℝ, Negligible e ∧ ∃ N' : ℕ, ∀ n∈S,N'≤n →
      ∀ B : Matrix (Fin n) (Fin n) ℤ,B.det≠0 → ∀ r : ℚ,0<r → dgsThreshold B≤(r:ℝ) → ∀ k : ℕ,
        ∃ b : ℕ, gridAdequate B (r:ℝ) (2^b) ∧ outputProb H (dgsInput B r 1 k)
           (fun out => ∃ z : Fin n→ℤ, encVec encI z <+: out)=1 ∧ ∀ T : Finset (Vec n),
          |outputProb H (dgsInput B r 1 k) (fun out => ∃ z∈T,encVec encI z <+: out)-
            fourierEvent B r (2^b) T|≤e n+1/(4*((k:ℝ)+1)) := by sorry

end InfoLossLAR.WorstCase.RegevSearch
