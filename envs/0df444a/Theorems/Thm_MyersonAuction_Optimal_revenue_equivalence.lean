-- Prove2me | Theorems.Thm_MyersonAuction_Optimal_revenue_equivalence
-- name    : MyersonAuction.Optimal.revenue_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:46:46.521989+00:00
-- url     : https://prove2.me/theorems/8a3444ed-efbb-46d5-b933-dd7a1bb59b0a
-- title:
--   Corollary — revenue-equivalence theorem
-- statement:
--   Consider two feasible direct mechanisms $(p,x)$ and $(p',x')$. If they have the same allocation probabilities at every supported type profile, and each bidder obtains the same interim utility at her lowest possible estimate, then the seller obtains the same expected utility:
--
--   $$
--   p_i(t)=p'_i(t)\ (t\in T),\quad U_i(p,x,a_i)=U_i(p',x',a_i)\ (i\in N)
--   \quad\Longrightarrow\quad U_0(p,x)=U_0(p',x').
--   $$
--
--   Thus payments affect the seller’s expected utility only through the lowest-type utilities once the allocation rule is fixed.
-- source:
--   Myerson, Optimal Auction Design, Math. Oper. Res. 6(1) (1981), p. 65, Corollary (The Revenue-Equivalence Theorem)

import Definitions.Def_MyersonAuction_Optimal_Mechanism

noncomputable section

namespace MyersonAuction.Optimal

theorem revenue_equivalence {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (E : Environment ι) (p x p' x' : Outcome ι)
    (h : Feasible E p x) (h' : Feasible E p' x')
    (hp : ∀ t ∈ support E, ∀ i, p i t = p' i t)
    (hu : ∀ i, interimUtility E p x i (E.a i) =
      interimUtility E p' x' i (E.a i)) :
    sellerUtility E p x = sellerUtility E p' x' := by sorry

end MyersonAuction.Optimal
