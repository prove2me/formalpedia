-- Prove2me | Theorems.Thm_HighDimStat_GraphicalModels_thm11_12_graph_selection_consistency
-- name    : HighDimStat.GraphicalModels.thm11_12_graph_selection_consistency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:22:23.951686+00:00
-- url     : https://prove2.me/theorems/b1b23aa0-9275-4b07-af35-91b0eadc95fb
-- title:
--   Graph selection consistency for Gaussian graphical models (Theorem 11.12)
-- statement:
--   **Theorem 11.12** (p. 361), the goal of this mission. There exist universal positive
--   constants $c_0,c_2,c_3$ (not depending on the problem instance) such that: let $\Theta^*$ be
--   the precision matrix of a zero-mean Gaussian vector with covariance
--   $\Sigma^*=(\Theta^*)^{-1}$, with true edges the off-diagonal nonzero entries of $\Theta^*$
--   and true neighborhoods $N(j)$. Suppose that for each $j$, $\Sigma^*_{\backslash\{j\}}$ is
--   $\alpha$-incoherent with respect to $N(j)$, $|\!|\!|(\Sigma^*_{N(j),N(j)})^{-1}|\!|\!|_\infty
--   \le b$ for some $b\ge1$, and the maximum degree is at most $m$. With
--   $\lambda_n=c_0\frac1\alpha\left(\sqrt{\log d/n}+\delta\right)$ for $\delta\in(0,1]$, the
--   neighborhood-Lasso estimate — solved independently at each vertex on $n$ i.i.d. Gaussian
--   samples — combined via *either* the AND or the OR rule, satisfies, with probability at
--   least $1-c_2e^{-c_3n\min(\delta^2,1/m)}$: (a) no false inclusions, $\hat E\subseteq E$;
--   (b) every significant edge $(j,k)$ with $|\Theta^*_{jk}|\ge7b\lambda_n$ is included.
--
--   This shows that a purely local, per-vertex procedure (solving $d$ separate Lasso problems)
--   recovers the global graph structure of a Gauss-Markov random field, at a sample complexity
--   governed by the incoherence parameter $\alpha$ and the maximum degree $m$, mirroring the
--   Lasso's own support-recovery guarantee (Chapter 7) but now for a random-design regression
--   problem induced by the graphical structure itself.
--
--   **Formalization Note** The theorem is stated with the conclusion holding jointly for both
--   the OR-rule and the AND-rule estimated edge sets (matching "based on either the AND or OR
--   rules" literally), on a single high-probability event. `d = Fintype.card V`; `n` and `m`
--   are cast to `ℝ` where the book's formula requires it. `c_0,c_2,c_3` are bound by a single
--   leading `∃` scoping over the entire rest of the statement (Revision 1): they are chosen once,
--   uniformly over every problem instance satisfying the hypotheses, matching the book's own
--   "there exist universal constants" reading of Theorem 11.12 rather than letting them be chosen
--   per-instance (which would make the claimed bound trivially satisfiable, e.g. by `c_3→∞`).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 361 (PDF p. 381), Theorem 11.12

import Mathlib
import Definitions.Def_HighDimStat_GraphicalModels_NeighborhoodLasso

namespace HighDimStat.GraphicalModels

open MeasureTheory

/-- **Theorem 11.12** (Graph selection consistency, p. 361, PDF 381), the goal of this
mission. `Θstar` is the precision matrix of a zero-mean Gaussian vector `X` with covariance
`Sigstar = Θstar⁻¹`; the true edges are the off-diagonal nonzero entries of `Θstar`, and
`N j` the true neighborhood of `j`. Suppose every `Sigstar` restricted off vertex `j` is
`α`-incoherent with respect to `N j` (Eq. 11.23), the `ℓ∞`-operator norm of the inverse of
`Sigstar` restricted to `N j × N j` is at most `b ≥ 1`, and every true degree is at most `m`.
With `λₙ = c₀(1/α)(√(log d/n) + δ)` for `δ ∈ (0,1]`, the neighborhood-Lasso estimate (solved
independently at every vertex, on `n` i.i.d. Gaussian samples), combined via *either* the
AND or the OR rule, satisfies, with probability at least `1 − c₂ e^{-c₃ n min(δ²,1/m)}`:
(a) no false inclusions (the estimated edge set is a subset of the true one); (b) every
significant true edge `(j,k)` with `|Θstar j k| ≥ 7bλₙ` is included. -/
theorem thm11_12_graph_selection_consistency :
    ∃ c0 c2 c3 : ℝ, 0 < c0 ∧ 0 < c2 ∧ 0 < c3 ∧
    ∀ {V Ω : Type*} [Fintype V] [DecidableEq V]
      [Nonempty V] [MeasurableSpace Ω] {n : ℕ}, 0 < n →
    ∀ (Θstar Sigstar : Matrix V V ℝ), Sigstar * Θstar = 1 →
    ∀ (trueNbhd : V → Finset V), (∀ j k, k ∈ trueNbhd j ↔ k ≠ j ∧ Θstar j k ≠ 0) →
    ∀ (α b : ℝ), 1 ≤ b →
      (∀ j, IsAlphaIncoherent Sigstar (Finset.univ.filter (· ≠ j)) (trueNbhd j) α) →
      (∀ j, opNormInfty (submatrixOn Sigstar (trueNbhd j))⁻¹ ≤ b) →
    ∀ (m : ℕ), 0 < m → (∀ j, (trueNbhd j).card ≤ m) →
    ∀ (P : Measure Ω) [IsProbabilityMeasure P] (Xdes : Fin n → Ω → V → ℝ),
      IsIIDGaussianDesign Xdes P Sigstar →
    ∀ (δ : ℝ), δ ∈ Set.Ioc (0 : ℝ) 1 →
    ∀ (lam : ℝ), lam = c0 * (1 / α) * (Real.sqrt (Real.log (Fintype.card V) / n) + δ) →
    ∀ (θhat : ∀ j : V, Ω → {k : V // k ≠ j} → ℝ),
      (∀ j ω, IsNeighborhoodLassoSolution Xdes j ω lam (θhat j ω)) →
      1 - c2 * Real.exp (-c3 * n * min (δ ^ 2) (1 / (m : ℝ))) ≤
        P.real {ω |
          (orRuleEdges (fun j => estimatedNeighborhood (θhat j ω)) ⊆
              {p : V × V | p.1 ≠ p.2 ∧ Θstar p.1 p.2 ≠ 0} ∧
            ∀ j k, j ≠ k → 7 * b * lam ≤ |Θstar j k| →
              (j, k) ∈ orRuleEdges (fun j => estimatedNeighborhood (θhat j ω))) ∧
          (andRuleEdges (fun j => estimatedNeighborhood (θhat j ω)) ⊆
              {p : V × V | p.1 ≠ p.2 ∧ Θstar p.1 p.2 ≠ 0} ∧
            ∀ j k, j ≠ k → 7 * b * lam ≤ |Θstar j k| →
              (j, k) ∈ andRuleEdges (fun j => estimatedNeighborhood (θhat j ω)))} := by sorry

end HighDimStat.GraphicalModels
