-- Prove2me | Theorems.Thm_IgnallSchrage_Invariance_sumCompletion_shift
-- name    : IgnallSchrage.Invariance.sumCompletion_shift
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:31.35201+00:00
-- url     : https://prove2.me/theorems/30e971e6-f61a-40b9-a2f2-62f8378b3946
-- title:
--   p. 411 — on two machines, adding $G$ raises $\sum_i d_i$ of every sequence by $\tfrac12 Gn(n+3)$
-- statement:
--   Consider $n$ jobs on two machines with nonnegative processing times $a_i,b_i$, and let $G>0$. Write $\sum_i d_i(\sigma)$ for the sum of the completion times of the full sequence $\sigma$, and $\sum_i \tilde d_i(\sigma)$ for the same sum after adding $G$ to every processing time. Then for every $\sigma$
--   $$
--   \sum_i \tilde d_i(\sigma)=\sum_i d_i(\sigma)+\sum_{r=1}^{n}G(r+1)=\sum_i d_i(\sigma)+\tfrac12\,G\,n(n+3).
--   $$
--
--   The same constant is added to the value of every sequence, so the set of optimal sequences is unchanged.
--
--   **Formalization Note** Nonnegative processing times are assumed, as for the completion-time shift.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 411, Appendix, proof of the THEOREM (sum of the completion times increased by ½Gn(n+3))

import Mathlib
import Definitions.Def_IgnallSchrage_Invariance_TwoMachine

namespace IgnallSchrage.Invariance

/-- p. 411: on two machines, adding `G` to all processing times (all nonnegative) raises the sum of the
completion times of every sequence by `Σ_{r=1}^{n} G (r + 1) = ½ G n (n + 3)`. -/
theorem sumCompletion_shift {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (G : ℝ) (hG : 0 < G)
    (σ : Equiv.Perm (Fin n)) :
    sumCompletion (fun i => a i + G) (fun i => b i + G) σ =
      sumCompletion a b σ + G * n * (n + 3) / 2 := by sorry

end IgnallSchrage.Invariance
