-- Prove2me | Theorems.Thm_JewellMRP_InfiniteStep_fundamental_matrix_cesaro
-- name    : JewellMRP.InfiniteStep.fundamental_matrix_cesaro
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:31:52.650444+00:00
-- url     : https://prove2.me/theorems/1494507c-2282-4393-a0c5-e1586012000d
-- title:
--   Appendix A, p. 966 — $I + \sum_{j=1}^{n-1}(P^j - \Pi)$ is Cesàro-summable to the fundamental matrix $Z$
-- statement:
--   Let $P$ be an irreducible row-stochastic matrix on a nonempty finite state set, $\pi$ its stationary probability vector, $\Pi$ the matrix all of whose rows equal $\pi$, and $Z = (I - P + \Pi)^{-1}$. Put
--   $$A(n) = I + \sum_{j=1}^{n-1}\bigl(P^j - \Pi\bigr), \qquad n \ge 1 .$$
--   Then the Cesàro means of $A(n)$ converge to $Z$:
--   $$\lim_{n\to\infty}\frac1n\sum_{m=1}^{n} A(m) = Z .$$
--
--   This identifies the fundamental matrix of Kemeny and Snell as the (Cesàro) sum of the deviations of the powers of $P$ from their limit, which is how $Z$ enters the limiting bias.
--
--   **Formalization Note** The paper says the sequence "converges or is Cesàro-summable"; for periodic chains only the Cesàro limit exists, and that is what is stated. $A(1) = I$ (empty sum).
-- source:
--   Jewell, Markov-Renewal Programming. II: Infinite Return Models, Example, Oper. Res. 11 (1963), p. 966, Appendix A (before Eq. (A 4))

import Mathlib
import Definitions.Def_JewellMRP_InfiniteStep_Model

open Matrix Filter Topology

namespace JewellMRP.InfiniteStep

theorem fundamental_matrix_cesaro {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ) (hπ : IsStationary P π) :
    Tendsto (cesaroMean (fun n : ℕ => 1 + ∑ j ∈ Finset.Ico 1 n, (P ^ j - limitMatrix π)))
      atTop (𝓝 (fundamentalMatrix P π)) := by sorry

end JewellMRP.InfiniteStep
