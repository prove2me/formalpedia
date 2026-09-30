-- Prove2me | Theorems.Thm_JewellMRP_InfiniteStep_stationary_cesaro_limit
-- name    : JewellMRP.InfiniteStep.stationary_cesaro_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:28:33.039994+00:00
-- url     : https://prove2.me/theorems/6d3dad52-f399-4624-8795-84d6a8e77845
-- title:
--   Appendix A, p. 966 — an ergodic chain has a unique, positive stationary vector and $P^n$ is Cesàro-summable to $\Pi$
-- statement:
--   Let $P$ be an irreducible row-stochastic matrix on a nonempty finite state set $S$. Then there is a probability vector $\pi$ with $\pi P = \pi$ such that
--
--   1. every entry of $\pi$ is strictly positive,
--   2. $\pi$ is the only stationary probability vector of $P$, and
--   3. the Cesàro means of the powers of $P$ converge entrywise to the matrix $\Pi$ whose rows all equal $\pi$:
--   $$\lim_{n\to\infty} \frac1n \sum_{k=0}^{n-1} P^k = \Pi .$$
--
--   This is the Markov-chain fact on which Appendix A rests: it identifies the limiting per-step reward $\Pi\rho$ and makes the matrix $\Pi$ used in the fundamental matrix well defined.
--
--   **Formalization Note** The paper says "$P^{n-1}$ converges or is Cesàro-summable"; ordinary convergence fails for periodic chains, so the statement is the Cesàro limit, which holds for every irreducible chain.
-- source:
--   Jewell, Markov-Renewal Programming. II: Infinite Return Models, Example, Oper. Res. 11 (1963), p. 966, Appendix A (after Eq. (A 1)), citing Kemeny and Snell [13]

import Mathlib
import Definitions.Def_JewellMRP_InfiniteStep_Model

open Matrix Filter Topology

namespace JewellMRP.InfiniteStep

theorem stationary_cesaro_limit {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : IsErgodic P) :
    ∃ π : S → ℝ, IsStationary P π ∧ (∀ i, 0 < π i) ∧
      (∀ π' : S → ℝ, IsStationary P π' → π' = π) ∧
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, P ^ k) atTop
        (𝓝 (limitMatrix π)) := by sorry

end JewellMRP.InfiniteStep
