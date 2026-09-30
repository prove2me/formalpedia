-- Prove2me | Theorems.Thm_JewellMRP_InfiniteStep_return_increment_cesaro
-- name    : JewellMRP.InfiniteStep.return_increment_cesaro
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:29:27.882988+00:00
-- url     : https://prove2.me/theorems/ddd77041-4902-4afb-8a5b-42f73a0402c1
-- title:
--   Eq. (A 2) — the return increments are Cesàro-convergent to $\Pi\rho = G\mathbf 1$
-- statement:
--   Let $P$ be an irreducible row-stochastic matrix on a nonempty finite state set with stationary probability vector $\pi$, let $\Pi$ be the matrix whose rows all equal $\pi$, and let $V(n)$ be the $n$-step return of the fixed policy for one-step rewards $\rho$ and arbitrary terminal rewards $V(0)$. Then
--   $$\lim_{n\to\infty}\frac1n\sum_{m=1}^{n}\bigl(V(m) - V(m-1)\bigr) = \Pi\rho, \qquad \text{and} \qquad (\Pi\rho)_i = \sum_{j}\pi_j\rho_j = G \ \text{ for all } i .$$
--
--   So the long-run per-transition increase of the expected return is the system gain $G$, the same from every starting state.
--
--   **Formalization Note** The paper writes $\lim_{n\to\infty} V(n) - V(n-1) = \Pi\rho$. For a periodic chain (such as the paper's own example) the increments oscillate and only their Cesàro means converge, so the limit is stated in the Cesàro sense. The statement holds for every terminal-reward vector $V(0)$.
-- source:
--   Jewell, Markov-Renewal Programming. II: Infinite Return Models, Example, Oper. Res. 11 (1963), p. 966, Eq. (A 2)

import Mathlib
import Definitions.Def_JewellMRP_InfiniteStep_Model

open Matrix Filter Topology

namespace JewellMRP.InfiniteStep

theorem return_increment_cesaro {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ) (hπ : IsStationary P π)
    (ρ V0 : S → ℝ) :
    Tendsto (cesaroMean (fun m => stepReturn P ρ V0 m - stepReturn P ρ V0 (m - 1))) atTop
        (𝓝 (limitMatrix π *ᵥ ρ)) ∧
      limitMatrix π *ᵥ ρ = fun _ => gain π ρ := by sorry

end JewellMRP.InfiniteStep
