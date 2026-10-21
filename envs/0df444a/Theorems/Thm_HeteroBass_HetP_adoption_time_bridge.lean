-- Prove2me | Theorems.Thm_HeteroBass_HetP_adoption_time_bridge
-- name    : HeteroBass.HetP.adoption_time_bridge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:01.986686+00:00
-- url     : https://prove2.me/theorems/8c08a337-77f8-47a0-956e-17b1936e94ac
-- title:
--   (32) and (61) — adoption-time law and expected count
-- statement:
--   Let a network have $M\ge2$ consumers, nonnegative external rates $p_j$ and edge rates $q_{k,j}$, positive total incoming peer influence $q_j$ for each consumer as assumed in (7), and a positive total adoption rate from every nonfull adopter set. Let $N(t)$ be the count in the generator-defined process and $T_m$ the time of its $m$th adoption. For $t\ge0$ and $1\le m\le M$,
--
--   $$\Pr(N(t)\ge m)=\Pr(T_m\le t),\qquad f(t)=\frac1M\sum_{m=1}^{M}\Pr(T_m\le t).$$
--
--   The identities connect the generator formulation of the model to its adoption-order and holding-time formulation.
--
--   **Formalization Note** The positive incoming peer influence is the paper's standing assumption (7). Positivity of all nonterminal stage rates additionally ensures that the jump-chain weights and exponential measures have their intended probability meaning.
-- source:
--   Fibich & Golan, Diffusion of new products with heterogeneous consumers, arXiv:2102.05926v3, §3.3, eq. (32), p. 10; Appendix D, eq. (61), p. 26

import Mathlib
import Definitions.Def_HeteroBass_HetP_Model

namespace HeteroBass.HetP

/-- (32) and (61): the generator and jump-chain descriptions of the same adoption process. -/
theorem adoption_time_bridge (M : ℕ) (hM : 2 ≤ M)
    (p : Fin M → ℝ) (Q : Fin M → Fin M → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hQ : ∀ k j, 0 ≤ Q k j)
    (hpeer : ∀ j, 0 < ∑ k ∈ Finset.univ.erase j, Q k j)
    (hstage : ∀ S : Finset (Fin M), S ≠ Finset.univ → 0 < totalRate p Q S)
    (t : ℝ) (ht : 0 ≤ t) :
    (∀ m : ℕ, 1 ≤ m → m ≤ M →
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin M) => m ≤ S.card),
        transition p Q t ∅ S) = adoptionTimeCDF p Q m t) ∧
    expectedFraction p Q t =
      (1 / (M : ℝ)) * ∑ m ∈ Finset.Icc 1 M, adoptionTimeCDF p Q m t := by sorry

end HeteroBass.HetP
