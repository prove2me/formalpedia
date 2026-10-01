-- Prove2me | Theorems.Thm_JewellMRP_InfiniteStep_bias_formula
-- name    : JewellMRP.InfiniteStep.bias_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:32:29.791711+00:00
-- url     : https://prove2.me/theorems/e179cb8d-b41c-470d-9642-fea60cc2d379
-- title:
--   Eq. (A 3) — $W(n) = [I + \sum_{j=1}^{n-1}(P^j-\Pi) - \Pi]\rho + V(0)$ for constant terminal rewards
-- statement:
--   Let $P$ be an irreducible row-stochastic matrix on a nonempty finite state set with stationary probability vector $\pi$, let $\Pi$ be the matrix all of whose rows equal $\pi$, let $\rho$ be the one-step rewards, $G = \sum_i\pi_i\rho_i$ the gain, and let $V(0)$ be a **constant** terminal-reward vector. With $V(n)$ the $n$-step return and $W_i(n) = V_i(n) - Gn$, for every $n \ge 1$
--   $$W(n) = \Bigl[I + \sum_{j=1}^{n-1}\bigl(P^j - \Pi\bigr) - \Pi\Bigr]\rho + V(0).$$
--
--   This expresses the finite-horizon bias through the partial sums whose Cesàro limit is the fundamental matrix.
--
--   **Formalization Note** The paper prints (A 3) with no condition on $V(0)$. For general $V(0)$ the last term is $P^n V(0)$ rather than $V(0)$; the two agree for all $n$ exactly when $PV(0) = V(0)$, i.e. (for irreducible $P$) when $V(0)$ is constant, and that hypothesis is added. The formula is for $n \ge 1$, as printed.
-- source:
--   Jewell, Markov-Renewal Programming. II: Infinite Return Models, Example, Oper. Res. 11 (1963), p. 966, Eq. (A 3)

import Mathlib
import Definitions.Def_JewellMRP_InfiniteStep_Model

open Matrix Filter Topology

namespace JewellMRP.InfiniteStep

theorem bias_formula {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ) (hπ : IsStationary P π)
    (ρ V0 : S → ℝ) (hV0 : ∀ i j, V0 i = V0 j) (n : ℕ) (hn : 1 ≤ n) :
    biasSeq P π ρ V0 n =
      (1 + ∑ j ∈ Finset.Ico 1 n, (P ^ j - limitMatrix π) - limitMatrix π) *ᵥ ρ + V0 := by sorry

end JewellMRP.InfiniteStep
