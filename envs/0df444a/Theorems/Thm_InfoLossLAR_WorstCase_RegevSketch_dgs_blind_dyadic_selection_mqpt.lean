-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dgs_blind_dyadic_selection_mqpt
-- name    : InfoLossLAR.WorstCase.RegevSketch.dgs_blind_dyadic_selection_mqpt
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-18T22:50:52.11238+00:00
-- url     : https://prove2.me/theorems/68fca3d6-1f6c-44c1-b5b1-ef4383a55f3b
-- title:
--   Uniform circuit for blind selection over dyadic DGS pools
-- statement:
--   Given the sampler and a fixed polynomial exponent for the dyadic grid, construct one uniform algorithm, independent of the approximation factor. For a dimension where joint DGS correctness holds, suppose every nonsingular basis has a grid scale above threshold with ideal short-spanning probability at least $7/8$ at the desired radius. Apply the additive event-error contract there with a constant unary budget and use negligibility to bound the count times the error. Run the sampler on all grid scales, decode each pool and map coefficients through the basis. On each pool find the independent tuple of smallest possible maximum squared norm by greedy rank tests in order of squared norm; among the resulting tuples retain the one with the smallest maximum. Invalid scales and malformed outputs cannot spoil a good tuple. The integer arithmetic, rank tests and encodings have polynomial cost in the input and measured-output size. Uniformly compose the independent sampler circuits at all required query lengths with this classical postprocessing.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, full version dated May 2, 2009, https://cims.nyu.edu/~regev/papers/qcrypto.pdf. Lemmas 3.15–3.17, full-version PDF pp. 28–29; fixed-family substitution and explicit uniform multi-output realization.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
set_option maxHeartbeats 200000
open QAlgorithms.Complexity
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch

theorem dgs_blind_dyadic_selection_mqpt :    ∀ (d : ℕ) (G : MFamily), IsMQPT G →
      ∀ (error : ℕ → ℝ), Negligible error →
        ∃ A : MFamily, IsMQPT A ∧ ∃ n₁ : ℕ, ∀ n ≥ n₁, 1 ≤ n →
          DGSAt G n (error n) → ∀ γ : ℝ,
          (∀ (B : Matrix (Fin n) (Fin n) ℤ), B.det ≠ 0 →
            ∃ j : ℕ, j ≤ ((encMat encI B).length + n + 2)^d ∧
              dgsThreshold B ≤ (2 : ℝ)^j ∧
              2 * Real.sqrt n * (2 : ℝ)^j ≤ γ * lamN B ∧
              (7 : ℝ)/8 ≤ ∑' pool : Fin (16 * (n + 1)^2) → Fin n → ℤ,
                (∏ i, coefficientMass B ((2 : ℝ)^j) (pool i)) *
                (if ∃ pick : Fin n → Fin (16 * (n + 1)^2),
                  LinearIndependent ℝ (fun i => latVec B (pool (pick i))) ∧
                    ∀ i, ‖latVec B (pool (pick i))‖ ≤ 2 * Real.sqrt n * (2 : ℝ)^j
                 then 1 else 0)) →
          SolvesSIVP A n γ := by sorry

end InfoLossLAR.WorstCase.RegevSketch
