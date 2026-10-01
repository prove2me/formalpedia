-- Prove2me | Theorems.Thm_JewellMRP_InfiniteStep_infinite_step_gain_bias
-- name    : JewellMRP.InfiniteStep.infinite_step_gain_bias
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:34:41.670702+00:00
-- url     : https://prove2.me/theorems/263ed794-6a3a-4740-8bd7-28c58348c62e
-- title:
--   Eqs. (A 4)–(A 7) — the infinite-step return is $V(n) \approx Gn + W$ with $G = \pi\rho$ and Cesàro bias $W = (Z-\Pi)\rho + \Pi V(0)$
-- statement:
--   Consider a Markov-renewal program operated under a fixed stationary policy whose embedded chain has transition matrix $P = (p_{ij})$ on a nonempty finite state set, assumed irreducible (ergodic; periodicity is allowed). Let $\pi$ be its stationary probability vector, $\Pi$ the matrix all of whose rows equal $\pi$, $\rho$ the vector of one-step expected rewards and $V(0)$ the vector of terminal rewards. Let $V(n)$ be the expected $n$-step return, $V(n) = \rho + PV(n-1)$, let
--   $$G = \sum_{i}\pi_i\rho_i \qquad \text{(A 6)}$$
--   be the system gain and $W_i(n) = V_i(n) - Gn$ the bias after $n$ steps. Then
--
--   1. the matrix $I - P + \Pi$ is invertible, so the fundamental matrix $Z = (I - P + \Pi)^{-1}$ (A 7) is well defined, and
--   2. the biases converge in the Cesàro sense to $(Z - \Pi)\rho + \Pi V(0)$:
--   $$\lim_{n\to\infty}\frac1n\sum_{m=1}^{n} W(m) = (Z - \Pi)\rho + \Pi V(0).$$
--
--   Componentwise, $V_i(n) \approx Gn - G + \sum_j z_{ij}\rho_j + \sum_j \pi_j V_j(0)$: the expected return grows linearly at rate $G$, independent of the initial state, with a state-dependent offset given by the fundamental matrix. This is the asymptotic form (1) that the paper's policy-improvement algorithm for the infinite-step model relies on.
--
--   **Formalization Note** Two printed slips are corrected. (i) The paper writes the limit as $[Z - \Pi]\rho + V(0)$; iterating (I 16) the terminal rewards contribute $P^nV(0)$, whose Cesàro limit is $\Pi V(0)$. The two coincide when $V(0)$ is constant, in particular in the paper's example ($V(0) = 0$), and only $\Pi V(0)$ is consistent with the paper's own equation (4). (ii) The paper writes an ordinary limit while stating that $P^{n-1}$ "converges or is Cesàro-summable"; for periodic chains, such as the paper's example, $W(n)$ oscillates, so the limit is taken in the Cesàro sense $\frac1n\sum_{m=1}^n W(m)$. The stationary vector $\pi$ is quantified over all stationary probability vectors of $P$, which under irreducibility is exactly one.
-- source:
--   Jewell, Markov-Renewal Programming. II: Infinite Return Models, Example, Oper. Res. 11 (1963), pp. 966-967, Eqs. (A 4)-(A 6); p. 952, Eqs. (A 5)-(A 7)

import Mathlib
import Definitions.Def_JewellMRP_InfiniteStep_Model

open Matrix Filter Topology

namespace JewellMRP.InfiniteStep

theorem infinite_step_gain_bias {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ) (hπ : IsStationary P π)
    (ρ V0 : S → ℝ) :
    IsUnit (1 - P + limitMatrix π) ∧
      Tendsto (cesaroMean (biasSeq P π ρ V0)) atTop
        (𝓝 ((fundamentalMatrix P π - limitMatrix π) *ᵥ ρ + limitMatrix π *ᵥ V0)) := by sorry

end JewellMRP.InfiniteStep
