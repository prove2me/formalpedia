-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_tendsto_variance_quadratic_matrix_forms_readable
-- name    : FunctionalInequalities.Probability.tendsto_variance_quadratic_matrix_forms_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:23.438743+00:00
-- url     : https://prove2.me/theorems/6bac75bd-e0cf-4ff6-8155-e85bb3d798fc
-- title:
--   Continuity of Variance for Quadratic Matrix Forms
-- statement:
--   This formalizes the coefficient-continuity part of Lemma A.2 of Letwin (arXiv:2607.24164v1), cited as “Reduction to invertible $M$.”
--
--   Let $\mu$ be a probability measure on $E=\mathrm{EuclideanSpace}\,\mathbb R\,(\mathrm{Fin}\,n)$ with finite fourth moment. Let $A_k$ and $A$ be real $n\times n$ matrices with $A_k\to A$ entrywise (equivalently in the finite-dimensional matrix topology). Then
--
--   $$\operatorname{Var}_{\mu}\!\left(x\mapsto\sum_{i,j}(A_k)_{ij}x_i x_j\right)
--   \longrightarrow
--   \operatorname{Var}_{\mu}\!\left(x\mapsto\sum_{i,j}A_{ij}x_i x_j\right).$$
--
--   The declaration supplies the fourth-moment continuity needed in singular extensions of matrix variance bounds; it does not itself assert a numerical variance estimate.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   set_option maxHeartbeats 500000 in
--   theorem tendsto_variance_quadratic_matrix_forms {n : ℕ}
--       (mu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
--       (h4 : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 4 (mu : Measure _))
--       {seq : ℕ → Matrix (Fin n) (Fin n) ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
--       (hseq : Tendsto seq atTop (𝓝 A)) :
--       Tendsto (fun k => ProbabilityTheory.variance
--         (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j, seq k i j * x i * x j) (mu : Measure _))
--         atTop (𝓝 (ProbabilityTheory.variance
--           (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j, A i j * x i * x j) (mu : Measure _)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/QuadraticVariance`](https://prove2.me/theorems/8f374ce2-317b-44db-96d6-94eef9130b1f).
--
--   Supporting theorems: [`tendsto_variance_finite_linear_combination`](https://prove2.me/theorems/dd0e74f6-3d24-47af-bea4-9a629c78de4f).
--
--   Next: [`quadratic_variance_le_centered_noise_convolution`](https://prove2.me/theorems/36dbece0-39c9-42e4-832b-b29a213eec41).
--
--   [Source excerpt, lines 23–32](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/QuadraticVariance.lean#L23-L32) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.2. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/QuadraticVariance.lean#L23-L53 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.QuadraticVariance`, declaration `FunctionalInequalities.Probability.tendsto_variance_quadratic_matrix_forms`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_QuadraticVariance

open MeasureTheory Filter Matrix
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 500000

theorem FunctionalInequalities.Probability.tendsto_variance_quadratic_matrix_forms_readable {n : ℕ}
    (mu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (h4 : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 4 (mu : Measure _))
    {seq : ℕ → Matrix (Fin n) (Fin n) ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hseq : Tendsto seq atTop (𝓝 A)) :
    Tendsto (fun k => ProbabilityTheory.variance
      (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j, seq k i j * x i * x j) (mu : Measure _))
      atTop (𝓝 (ProbabilityTheory.variance
        (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j, A i j * x i * x j) (mu : Measure _))) := by sorry
