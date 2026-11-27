-- Prove2me | Theorems.Thm_OnlineMatchFrameworks_Supplement_theorem_5
-- name    : OnlineMatchFrameworks.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:27:19.285412+00:00
-- url     : https://prove2.me/theorems/c1315a26-b8b5-5dc4-bd6b-71995c161d52
-- title:
--   Theorem 5: the index rule $w_ip_i/(p_i+(1-p_i)r_i)$ is optimal under item hazard rates
-- statement:
--   A single customer is offered items $i\in U$, a finite set, with probabilities $p_i\in[0,1]$ and weights $w_i\ge0$. After a failed offer of item $i$ the customer leaves with probability $r_i\in[0,1]$. Let $l$ list every item once, in nonincreasing order of the index
--
--   $$
--   \frac{w_ip_i}{p_i+(1-p_i)r_i}.
--   $$
--
--   Then offering the items in the order $l$ maximizes the expected weight of the matched item:
--
--   $$
--   \mathrm{star}(l)=\mathrm{OPT}(U,v).
--   $$
--
--   Ties may be broken in any way. The theorem solves the star problem exactly in this patience model, so it supplies a black box with $\kappa=1$ for the results of Section 4.
--
--   Differences from the source:
--   - encoding: the optimal strategy of a single customer without knowledge of the patience → the published star optimum, the maximum over duplicate-free lists; reason: the only feedback while the customer is present is a failure, so lists are all the deterministic strategies (p.16)
--   - reading: decreasing order of the index → any list of all the items, each once, in nonincreasing order; reason: ties must be allowed; every way of breaking them is optimal, which is the stronger reading
--   - encoding: the index w_i p_i/(p_i + (1 − p_i) r_i) → Lean division, which gives 0 when p_i = r_i = 0; reason: only the undefined case is affected: such an item can be neither bought nor end the process, so its position changes nothing
--   - reading: hazard rate r_i of each item, a probability (p.22); weights with no sign stated → 0 ≤ r_i ≤ 1 and w ≥ 0; reason: the standing conventions of §5.1 and of the paper
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, Theorem 5, p.23

import Definitions.Def_OnlineMatchFrameworks_StarPolicy
import Definitions.Def_OnlineMatchFrameworks_PatienceModels

namespace OnlineMatchFrameworks.Supplement

/-- **Theorem 5.** arXiv:1907.03963v6, Theorem 5, p.23: "For maximizing the expected weight of the
matched item in the (item-dependent) Constant Hazard Rate patience model, it is optimal to probe items
in decreasing order of w_i p_i / (p_i + (1 − p_i) r_i)."

**Formalization Note.** The customer is `() : Unit`. `l` is any list of all the items, each once, in
nonincreasing order of the index; ties may be in any order. An item with `p_i = r_i = 0` has index `0`
by Lean's `x/0 = 0`: it can be neither bought nor make the customer leave, so its place is irrelevant.
Optimal means equal to the published star optimum over all items. -/
theorem theorem_5 {U : Type*} [Fintype U] [DecidableEq U]
    (G : OnlineMatchFrameworks.Instance U Unit) (r : U → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1)
    (hS : ∀ l, G.surv () l = OnlineMatchFrameworks.hazardSurvival (fun i _ => r i) () l)
    (l : List U) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    (hsorted : l.Pairwise fun i j =>
      G.w j * G.p j () / (G.p j () + (1 - G.p j ()) * r j) ≤
        G.w i * G.p i () / (G.p i () + (1 - G.p i ()) * r i)) :
    G.starValue () l = G.starOpt Finset.univ () := by sorry

end OnlineMatchFrameworks.Supplement
