-- Prove2me | Theorems.Thm_MultiInterm_Compete_proposition_5_3
-- name    : MultiInterm.Compete.proposition_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:43:38.059196+00:00
-- url     : https://prove2.me/theorems/9b6d9fd4-53cf-4f0d-b27c-7d5d1ce75bbf
-- title:
--   Proposition 5.3 — efficiency and zero upstream revenue at zero downstream reserves
-- statement:
--   Let $n>2$ bidders have independent values with the atomless regular law $D$ on $[0,\bar v]$, where $\bar v$ may be infinite. Fix both downstream reserves at zero and a symmetric continuation Bayes–Nash equilibrium $s$ in weakly undominated strategies, with four strictly increasing mode-specific bid functions. Both downstream auctions are second-price with their stated reserves; upstream is second-price with reserve zero and own-bid merging. Deviations and attachments are unrestricted.
--
--   Every such continuation equilibrium is downstream efficient and surplus-optimal, and upstream revenue is zero almost surely:
--   $$\Pr[P_i^{\rm up}=0\text{ for all bidders }i]=1.$$
--   Downstream efficiency maximizes total upstream bidder utility; surplus optimality awards the item to the highest-valued bidder almost surely. This is the fixed-reserve setting of §5, so no intermediary best-response hypothesis is imposed.
--
--   Differences from the source:
--   - encoding: nonnegative real values and reserves; bidders 1 through n; intermediaries A and B → nonnegative-real carriers, Fin n bidders, and Bool intermediaries (false=A, true=B); reason: these are relabelings of the same spaces; the support endpoint may still be infinite
--   - encoding: finite bundles of own upstream bids and uniform random tie-breaking → one optional attachment per downstream bid, own-bid maximum merging, and exact finite outcome weights; reason: footnote 4 and §5.2.1 identify the effective bundle with its maximum; absence and zero remain distinct
--   - encoding: expectations with potentially unbounded values and payments → nonnegative integrals for revenues and finite interim benefit minus extended expected payment for utility; reason: preserves infinite expectations and unrestricted deviations without assuming a finite mean or integrable payments
--   - reading: four strictly increasing bid functions with possibly randomized participation → arbitrary measurable mixtures over abstention, two single-homing modes and multi-homing, with increasing functions on the value support; reason: the brief and §3.1 distinguish mode-specific bids from participation; the hypothesis imposes no restriction on attachments
--   - encoding: atomless regular D on [0, v̄] → the referenced regular continuous component, full interval support, and zeroMass=0; reason: this specifies the same density and virtual-value convention with no finite-mean condition
--   - reading: strictly monotone bid functions → strictly increasing functions; reason: the source uses monotone for increasing in its proof and in the ensuing §6.2 formulation
--   - reading: surplus optimal → almost-sure allocation to a highest-valued bidder; reason: the allocation reading used in the brief and Definition 6.5 remains meaningful for infinite means
--   - encoding: downstream winners maximize the sum of upstream utilities → their conditional upstream utility is maximal over all feasible two-slot assignments and attached bids; reason: this spells out the feasible allocations in §5.1; the upstream zero-reserve auction can attain the highest value by assigning both slots to that bidder
--   - generalization: single-homers bid zero in the other downstream auction (p. 10) → a single-homer's other auction receives a zero bid or no bid; reason: at a positive reserve a zero bid does not meet it, so both give the same outcome; at a zero reserve the source notes bidding zero dominates abstaining (p. 10); the source's zero-bid strategies are a special case
-- source:
--   Ganesh, Moallemi, Weinberg, On the Power and Limitations of Multiple Intermediaries for Single-Item Auctions, STOC 2027 submission (sha256 bdc0557e98c014301646135a34b1532361d0f6133aa7832c59b68394fa2a81dc), p. 13 (PDF 14), Proposition 5.3; zero-reserve setting p. 12 (PDF 13); proof pp. 28–29 (PDF 29–30)

import Definitions.Def_MultiInterm_Compete_Efficiency

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MultiInterm.Compete

theorem proposition_5_3 (D : ValueDistribution) (hD : D.zeroMass = 0) (n : ℕ) (hn : 2 < n)
    (s : BidderStrategy) (hs : Continuation D n (fun _ => 0) s) :
    DownstreamEfficient D n s (fun _ => 0) ∧ SurplusOptimal D n s (fun _ => 0) ∧
      AlmostSurely D n s (fun _ => 0) (fun z w u => ∀ i, upstreamPayment z w u i = 0) := by sorry

end MultiInterm.Compete
