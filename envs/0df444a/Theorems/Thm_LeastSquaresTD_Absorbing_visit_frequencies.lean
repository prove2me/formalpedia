-- Prove2me | Theorems.Thm_LeastSquaresTD_Absorbing_visit_frequencies
-- name    : LeastSquaresTD.Absorbing.visit_frequencies
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:02:20.192839+00:00
-- url     : https://prove2.me/theorems/c020f687-4e8c-4c01-a443-0b745456700e
-- title:
--   Proof of Theorem 1 — trial visit frequencies
-- statement:
--   For an absorbing finite Markov chain started according to $S$, suppose every state is reachable from the positive support of $S$. Run independent trials by restarting from $S$ after an absorbing state. Then there is a deterministic vector $\pi$ such that almost surely every state is visited infinitely often and the empirical proportion of in-trial departures from each state $x$ converges to $\pi_x$. Moreover $\pi_x>0$ for each non-absorbing state and $\pi_x=0$ for each absorbing state.
--
--   $$
--   \frac{1}{n}\#\{k<n:Z_k\in\mathcal N,\ Z_k=x\}\longrightarrow\pi_x\quad\text{almost surely}.
--   $$
--
--   These frequency properties supply the diagonal weights in Lemma 5 and the rank argument for Theorem 1.
--
--   **Formalization Note** The paper does not define “inaccessible”; it is reachability from the support of $S$. Its $\pi_x$ is expected departures per trial, while the displayed limit uses restart-process steps. The two vectors differ by a common positive scaling factor, which cancels from the LS TD limit.
-- source:
--   Bradtke and Barto, Linear Least-Squares Algorithms for Temporal Difference Learning, Machine Learning 22 (1996), https://doi.org/10.1023/A:1018056104778, p. 44, Proof of Theorem 1, first two sentences; p. 43, definition of π

import Definitions.Def_LeastSquaresTD_Absorbing_Estimator

namespace LeastSquaresTD.Absorbing

open MeasureTheory Filter Topology

/-- Proof of Theorem 1, p. 44, first two sentences. The paper calls `π x` the
expected number of departures from `x` per trial. With `n` indexing restart
steps, the limit here differs by one common positive time-scale factor;
the expression in Lemma 5 is invariant under that factor. -/
theorem visit_frequencies
    {X Ω : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Chain X) (S : X → ℝ) (Z : ℕ → Ω → X)
    (habs : C.IsAbsorbing) (hS_nonneg : ∀ x, 0 ≤ S x)
    (hS_sum : ∑ x, S x = 1) (haccess : C.AllAccessible S)
    (hlaw : HasRestartLaw C S μ Z) :
    ∃ π : X → ℝ,
      (∀ x : C.Nonabsorbing, 0 < π x.val) ∧
      (∀ x, C.P x x = 1 → π x = 0) ∧
      (∀ᵐ ω ∂μ, (∀ (x : X) (N : ℕ), ∃ n ≥ N, Z n ω = x) ∧
        (∀ x, Tendsto (fun n => outFrequency C (fun k => Z k ω) x n)
          atTop (𝓝 (π x)))) := by sorry

end LeastSquaresTD.Absorbing
