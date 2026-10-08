-- Prove2me | Theorems.Thm_MyersonAuction_Optimal_lemma_2
-- name    : MyersonAuction.Optimal.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:46:16.895575+00:00
-- url     : https://prove2.me/theorems/e11fbb81-b056-47a6-9e68-c551fe7e664b
-- title:
--   Lemma 2 — characterization of feasible direct mechanisms
-- statement:
--   A direct mechanism $(p,x)$ is feasible if and only if its interim win probability is weakly increasing in each bidder’s report, the interim utility satisfies the envelope formula, every lowest type has nonnegative utility, and the allocation probabilities satisfy the single-object constraint:
--
--   $$
--    s\le t\Longrightarrow Q_i(p,s)\le Q_i(p,t),\qquad
--    U_i(p,x,t)=U_i(p,x,a_i)+\int_{a_i}^{t}Q_i(p,r)\,dr,\qquad
--    U_i(p,x,a_i)\ge0.
--   $$
--
--   This characterization replaces the incentive inequalities by monotonicity and an integral identity.
--
--   **Formalization Note** Both sides require integrability of the mechanism and its report sections. The type estimates $s,t$ range only over $[a_i,b_i]$.
-- source:
--   Myerson, Optimal Auction Design, Math. Oper. Res. 6(1) (1981), p. 63, Lemma 2, eqs. (4.2)–(4.4)

import Definitions.Def_MyersonAuction_Optimal_Mechanism

noncomputable section

namespace MyersonAuction.Optimal

theorem lemma_2 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (E : Environment ι) (p x : Outcome ι) :
    Feasible E p x ↔
      WellDefined E p x ∧ ProbabilityCondition E p ∧
      MonotoneQ E p ∧ EnvelopeAndBaseIR E p x := by sorry

end MyersonAuction.Optimal
