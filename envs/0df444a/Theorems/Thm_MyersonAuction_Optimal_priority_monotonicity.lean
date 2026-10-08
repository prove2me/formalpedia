-- Prove2me | Theorems.Thm_MyersonAuction_Optimal_priority_monotonicity
-- name    : MyersonAuction.Optimal.priority_monotonicity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:59:57.13799+00:00
-- url     : https://prove2.me/theorems/193ab980-b833-4866-8c82-fd574857c4a0
-- title:
--   Section 6 — ironed priorities and the proposed win probabilities are increasing
-- statement:
--   Each ironed priority $\bar c_i(s)$ is weakly increasing on bidder $i$’s support. Consequently, the proposed mechanism’s interim win probability is weakly increasing:
--
--   $$
--   s\le t\Longrightarrow \bar c_i(s)\le\bar c_i(t)
--   \quad\text{and}\quad Q_i(\bar p,s)\le Q_i(\bar p,t)
--   \qquad(s,t\in[a_i,b_i]).
--   $$
--
--   This verifies the incentive-relevant monotonicity condition (4.2) for the allocation in the main theorem.
-- source:
--   Myerson, Optimal Auction Design, Math. Oper. Res. 6(1) (1981), p. 70, §6, paragraph following eq. (6.12)

import Definitions.Def_MyersonAuction_Optimal_Ironing

noncomputable section

namespace MyersonAuction.Optimal

theorem priority_monotonicity {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (E : Environment ι) :
    (∀ i, MonotoneOn (ironedPriority E i) (Set.Icc (E.a i) (E.b i))) ∧
      MonotoneQ E (pbar E) := by sorry

end MyersonAuction.Optimal
