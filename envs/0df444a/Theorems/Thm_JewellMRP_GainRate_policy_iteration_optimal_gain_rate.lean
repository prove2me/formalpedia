-- Prove2me | Theorems.Thm_JewellMRP_GainRate_policy_iteration_optimal_gain_rate
-- name    : JewellMRP.GainRate.policy_iteration_optimal_gain_rate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:27:42.061096+00:00
-- url     : https://prove2.me/theorems/c94e9c38-05ba-49af-b158-1184e5ea8670
-- title:
--   Fig. 2: policy iteration terminates at a stationary policy of maximal gain rate (B 7)
-- statement:
--   Let a Markov-renewal program have $N \ge 1$ states, a finite nonempty set of alternatives, positive mean sojourn times $\nu^z_i$, and an irreducible chain for every stationary policy (standing assumption 2). Consider any run of the algorithm of Fig. 2: policies $z_0, z_1, z_2, \dots$ (with $z_0$ arbitrary) and pairs $(g_k, v_k)$ such that, for every $k$,
--
--   1. $(g_k, v_k)$ solves the value-determination equations (13) of $z_k$, with $v_{k,N} = 0$, and
--   2. in each state $i$, $z_{k+1}(i)$ maximizes the test quantity $\frac{1}{\nu^z_i}\{\rho^z_i + \sum_j p^z_{ij} v_{k,j} - v_{k,i}\}$ over the alternatives $z$, and $z_{k+1}(i) = z_k(i)$ whenever $z_k(i)$ already attains the maximum.
--
--   Then the algorithm terminates: there is a $K$ with $z_{K+1} = z_K$. Moreover, whenever $z_{K+1} = z_K$, the number $g_K$ is the gain rate of $z_K$, and $z_K$ is an optimal stationary policy: for every stationary policy $z'$ and all stationary probability vectors $\pi$ of $z_K$'s chain and $\pi'$ of $z'$'s chain,
--   $$g_K = \frac{\sum_i \pi_i \rho^{z_K(i)}_i}{\sum_k \pi_k \nu^{z_K(k)}_k} \;\ge\; \frac{\sum_i \pi'_i \rho^{z'(i)}_i}{\sum_k \pi'_k \nu^{z'(k)}_k}.$$
--
--   This is the main algorithmic claim of the paper for the infinite-time undiscounted Markov-renewal program: policy iteration with the ratio test quantity finds a stationary policy whose gain rate is at least that of any other stationary policy.
--
--   **Formalization Note** The theorem quantifies over every run, i.e. over every choice among tied maximizers; only the retain-on-tie rule is imposed. The gain rate is the closed form (B 7); its interpretation as the long-run return per unit time (B 6) is not part of the statement.
-- source:
--   Jewell, Markov-Renewal Programming. II: Infinite Return Models, Example, Oper. Res. 11 (1963), pp. 954-955 (algorithm claim and termination claim), p. 956 Fig. 2, p. 954 Eq. (B 7), p. 951 assumptions 1-3

import Mathlib
import Definitions.Def_JewellMRP_GainRate_MRP
import Definitions.Def_JewellMRP_GainRate_PolicyIteration

namespace JewellMRP.GainRate
theorem policy_iteration_optimal_gain_rate {N : ℕ} [NeZero N] {α : Type*} [Fintype α]
    [Nonempty α] (M : MRP N α) (hM : M.IsErgodic) (z : ℕ → Fin N → α) (g : ℕ → ℝ)
    (v : ℕ → Fin N → ℝ) (hrun : M.IsPolicyIterationRun z g v) :
    (∃ K, z (K + 1) = z K) ∧
      ∀ K, z (K + 1) = z K →
        (∀ π : Fin N → ℝ, IsStationaryDist (M.policyMatrix (z K)) π →
            g K = M.gainRate (z K) π) ∧
          ∀ (z' : Fin N → α) (π π' : Fin N → ℝ),
            IsStationaryDist (M.policyMatrix (z K)) π →
            IsStationaryDist (M.policyMatrix z') π' →
            M.gainRate z' π' ≤ M.gainRate (z K) π := by sorry
end JewellMRP.GainRate
