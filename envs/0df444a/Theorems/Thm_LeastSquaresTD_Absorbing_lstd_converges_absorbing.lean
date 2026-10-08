-- Prove2me | Theorems.Thm_LeastSquaresTD_Absorbing_lstd_converges_absorbing
-- name    : LeastSquaresTD.Absorbing.lstd_converges_absorbing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:03:02.188013+00:00
-- url     : https://prove2.me/theorems/73d41edf-05f7-417c-86cc-ddbef346ef64
-- title:
--   Theorem 1 — probability-one convergence of trial-based LS TD
-- statement:
--   Let $P$ be the transition matrix of a finite absorbing Markov chain, $S$ a start distribution from which no state is inaccessible, and $R$ a transition reward that is zero whenever both endpoints are absorbing. Suppose the feature vectors of non-absorbing states are linearly independent, absorbing feature vectors vanish, the feature dimension is exactly the number of non-absorbing states, and $0\le\gamma\le1$. Apply the trial-based LS TD algorithm of Figure 2. Then there is a finite parameter $\theta^*$ whose features represent the true expected-return value function, and the algorithm's parameter estimate converges to it with probability one:
--
--   $$
--   V(x)=\phi_x^\top\theta^*\ (x\in X),\qquad
--   \theta_n\longrightarrow\theta^*\quad\text{almost surely}.
--   $$
--
--   The claim includes convergence of the value series at each state, including the undiscounted case $\gamma=1$.
--
--   **Formalization Note** “Absorbing” means an absorbing state is reachable from every state; “no inaccessible states” means reachability from the support of $S$. Figure 2 is represented by the restart process with its Markov path law. Only in-trial transitions enter (11); counting restart steps repeats estimates and does not change the limit. The factors $1/t$ cancel. The parameter $\theta^*$ is existential and represents the return-defined $V$, rather than being defined by the matrix limit. Lean's total matrix inverse supplies temporary values when early estimates are singular.
-- source:
--   Bradtke and Barto, Linear Least-Squares Algorithms for Temporal Difference Learning, Machine Learning 22 (1996), https://doi.org/10.1023/A:1018056104778, p. 43, Theorem 1; p. 42, Figure 2 and Eq. (11)

import Definitions.Def_LeastSquaresTD_Absorbing_Estimator

namespace LeastSquaresTD.Absorbing

open MeasureTheory Filter Topology

variable {m : ℕ}

/-- Theorem 1, p. 43. The paper's finite `θ*` is an existential parameter
representing the return-defined value function; at `γ = 1` the summability
is explicit. Figure 2 is read as a restart process, with only in-trial
transitions entering (11). `n` counts restart steps, repeating the estimate
at restart draws; this has the same asymptotic limit as trial time. -/
theorem lstd_converges_absorbing
    {X Ω : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Chain X) (S : X → ℝ) (R : X → X → ℝ)
    (φ : X → Fin m → ℝ) (γ : ℝ) (Z : ℕ → Ω → X)
    (habs : C.IsAbsorbing) (hS_nonneg : ∀ x, 0 ≤ S x)
    (hS_sum : ∑ x, S x = 1) (haccess : C.AllAccessible S)
    (hRabs : ∀ x y, C.P x x = 1 → C.P y y = 1 → R x y = 0)
    (hm : m = Fintype.card C.Nonabsorbing)
    (hli : LinearIndependent ℝ (fun x : C.Nonabsorbing => φ x.val))
    (hφabs : ∀ x, C.P x x = 1 → φ x = 0)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hlaw : HasRestartLaw C S μ Z) :
    ∃ θstar : Fin m → ℝ,
      (∀ x, Summable (fun k : ℕ => γ ^ k *
        (Matrix.mulVec (C.P ^ k) (C.rbar R)) x)) ∧
      (∀ x, C.value R γ x = ∑ i, φ x i * θstar i) ∧
      (∀ᵐ ω ∂μ, Tendsto
        (fun n => lstdTheta C R φ γ (fun k => Z k ω) n)
        atTop (𝓝 θstar)) := by sorry

end LeastSquaresTD.Absorbing
