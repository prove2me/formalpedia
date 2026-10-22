-- Prove2me | Theorems.Thm_KellyStochasticNetworks_RandomAccessCapacity_capacity_coverage
-- name    : KellyStochasticNetworks.RandomAccessCapacity.capacity_coverage
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:48:25.531554+00:00
-- url     : https://prove2.me/theorems/fd07c601-a66f-447a-ab09-f2e7851f7fcc
-- title:
--   Theorem 5.17 — interior capacity coverage by finite attempt rates
-- statement:
--   Let $G$ be a finite simple interference graph on the station set $R$. Let $S\subseteq\{0,1\}^R$ be its independent activity vectors, including the empty schedule. Define
--
--   $$\Lambda=\left\{\lambda\ge0:\exists p:S\to[0,\infty),\ \sum_{n\in S}p(n)=1,\ \sum_{n\in S}p(n)n_r\ge\lambda_r\text{ for all }r\in R\right\}.$$
--
--   For every arrival vector $\lambda$ in the ordinary interior of $\Lambda$, there is a finite real parameter vector $\theta\in\mathbb R^R$ such that
--
--   $$\mathbb E_\theta[n_r]=\frac{\sum_{n\in S}n_r\exp(\sum_i n_i\theta_i)}{\sum_{n\in S}\exp(\sum_i n_i\theta_i)}>\lambda_r\qquad(r\in R).$$
--
--   Here the expectation is under the equilibrium law (5.8) of the rate-$\exp(\theta_r)$ activation, unit-rate deactivation chain. Thus fixed finite attempt parameters can simultaneously provide strictly greater service at every station than any interior arrival vector requires.
--
--   **Formalization Note** Interior is ambient Euclidean interior and the conclusion is strictly coordinatewise. No feasibility of a Gibbs parameter is assumed. The finite graph is indexed by `Fin d`, with binary `Fin 2` activity coordinates; $d=0$ is allowed and gives the empty coordinatewise conclusion. This theorem does not assert queue stability for an adaptive or collision-prone system.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 126 (PDF p. 134), proof on printed pp. 127–128 (PDF pp. 135–136), Theorem 5.17. DOI: 10.1017/cbo9781139565363.

import Definitions.Def_KellyStochasticNetworks_RandomAccessCapacity_Network

namespace KellyStochasticNetworks.RandomAccessCapacity

theorem capacity_coverage {d : ℕ} (G : SimpleGraph (Fin d)) [DecidableRel G.Adj]
    (arrival : Fin d → ℝ) :
    let S := {n : Fin d → Fin 2 // ∀ i j, G.Adj i j → n i = 0 ∨ n j = 0}
    let Λ : Set (Fin d → ℝ) :=
      {v | (∀ r, 0 ≤ v r) ∧ ∃ p : S → ℝ,
        (∀ n, 0 ≤ p n) ∧ (∑ n, p n) = 1 ∧
          ∀ r, v r ≤ ∑ n : S, p n * (n.val r : ℝ)}
    arrival ∈ interior Λ → ∃ θ : Fin d → ℝ, ∀ r,
      arrival r < (∑ n : S, (n.val r : ℝ) * Real.exp (∑ i, (n.val i : ℝ) * θ i)) /
        (∑ n : S, Real.exp (∑ i, (n.val i : ℝ) * θ i)) := by sorry

end KellyStochasticNetworks.RandomAccessCapacity
