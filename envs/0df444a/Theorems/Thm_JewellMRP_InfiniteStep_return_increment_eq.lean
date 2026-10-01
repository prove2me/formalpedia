-- Prove2me | Theorems.Thm_JewellMRP_InfiniteStep_return_increment_eq
-- name    : JewellMRP.InfiniteStep.return_increment_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:29:03.298433+00:00
-- url     : https://prove2.me/theorems/8fd6b935-e009-49b5-ba12-d004e4a88a60
-- title:
--   Eq. (A 1) — $V(n) - V(n-1) = P^{n-1}\rho$ for constant terminal rewards
-- statement:
--   Let $P$ be an irreducible row-stochastic matrix on a nonempty finite state set, $\rho$ a vector of one-step expected rewards, and $V(0)$ a **constant** terminal-reward vector ($V_i(0) = V_j(0)$ for all $i, j$). Let $V(n)$ be the $n$-step expected return of the fixed policy, $V(n) = \rho + P V(n-1)$. Then for every $n \ge 1$
--   $$V(n) - V(n-1) = P^{n-1}\rho .$$
--
--   This is the first step of Appendix A: the increments of the return are the images of $\rho$ under the powers of $P$.
--
--   **Formalization Note** The paper prints (A 1) with no condition on $V(0)$. Iterating (I 16) gives $V(n) - V(n-1) = P^{n-1}(\rho + P V(0) - V(0))$, so (A 1) holds exactly when $P V(0) = V(0)$, which for an irreducible $P$ means that $V(0)$ is constant; that hypothesis is added here. It covers the paper's example, where $V(0) = 0$.
-- source:
--   Jewell, Markov-Renewal Programming. II: Infinite Return Models, Example, Oper. Res. 11 (1963), p. 966, Eq. (A 1)

import Mathlib
import Definitions.Def_JewellMRP_InfiniteStep_Model

open Matrix Filter Topology

namespace JewellMRP.InfiniteStep

theorem return_increment_eq {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : IsErgodic P) (ρ V0 : S → ℝ) (hV0 : ∀ i j, V0 i = V0 j)
    (n : ℕ) (hn : 1 ≤ n) :
    stepReturn P ρ V0 n - stepReturn P ρ V0 (n - 1) = (P ^ (n - 1)) *ᵥ ρ := by sorry

end JewellMRP.InfiniteStep
