-- Prove2me | Theorems.Thm_MultiInterm_Compete_corollary_6_6
-- name    : MultiInterm.Compete.corollary_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:43:33.774107+00:00
-- url     : https://prove2.me/theorems/9c1369dc-2cc1-4957-8407-9f84177a4fe1
-- title:
--   Corollary 6.6 — a continuation equilibrium has an allocation threshold
-- statement:
--   Let $n\ge3$ bidders have independent values with the atomless regular law $D$ on $[0,\bar v]$, where $\bar v$ may be infinite. Fix downstream reserves $r=(r_A,r_B)$ and a symmetric continuation Bayes–Nash equilibrium $s$ in weakly undominated strategies, with four strictly increasing mode-specific bid functions. Both downstream auctions are second-price with their stated reserves; upstream is second-price with reserve zero and own-bid merging. Deviations and attachments are unrestricted.
--
--   There exists a finite nonnegative threshold $\tau$ such that this equilibrium is surplus-optimal up to $\tau$: the highest-valued bidder receives the item when its value exceeds $\tau$, and otherwise there is no sale, almost surely. Moreover,
--   $$v<\tau\Longrightarrow\text{neither reserve is met},\qquad v>\tau\Longrightarrow\text{at least one reserve is met},$$
--   almost surely over types and their mixed actions. Types exactly at the threshold are unrestricted by the participation clause. This characterizes every such continuation equilibrium, without asserting existence of an equilibrium.
--
--   Differences from the source:
--   - encoding: nonnegative real values and reserves; bidders 1 through n; intermediaries A and B → nonnegative-real carriers, Fin n bidders, and Bool intermediaries (false=A, true=B); reason: these are relabelings of the same spaces; the support endpoint may still be infinite
--   - encoding: finite bundles of own upstream bids and uniform random tie-breaking → one optional attachment per downstream bid, own-bid maximum merging, and exact finite outcome weights; reason: footnote 4 and §5.2.1 identify the effective bundle with its maximum; absence and zero remain distinct
--   - encoding: expectations with potentially unbounded values and payments → nonnegative integrals for revenues and finite interim benefit minus extended expected payment for utility; reason: preserves infinite expectations and unrestricted deviations without assuming a finite mean or integrable payments
--   - reading: four strictly increasing bid functions with possibly randomized participation → arbitrary measurable mixtures over abstention, two single-homing modes and multi-homing, with increasing functions on the value support; reason: the brief and §3.1 distinguish mode-specific bids from participation; the hypothesis imposes no restriction on attachments
--   - encoding: atomless regular D on [0, v̄] → the referenced regular continuous component, full interval support, and zeroMass=0; reason: this specifies the same density and virtual-value convention with no finite-mean condition
--   - reading: the game yields a surplus-optimal equilibrium up to a threshold → every continuation equilibrium satisfying the section assumptions has such a threshold; reason: this is the property proved in Appendix C.4, not an additional equilibrium-existence claim
--   - reading: types below τ enter neither auction → types below τ abstain or bid below the reserve in both auctions; reason: Appendix C.4 explicitly says abstains (or bids below the reserve); entering means effective entry
--   - generalization: single-homers bid zero in the other downstream auction (p. 10) → a single-homer's other auction receives a zero bid or no bid; reason: at a positive reserve a zero bid does not meet it, so both give the same outcome; at a zero reserve the source notes bidding zero dominates abstaining (p. 10); the source's zero-bid strategies are a special case
-- source:
--   Ganesh, Moallemi, Weinberg, On the Power and Limitations of Multiple Intermediaries for Single-Item Auctions, STOC 2027 submission (sha256 bdc0557e98c014301646135a34b1532361d0f6133aa7832c59b68394fa2a81dc), p. 16 (PDF 17), Corollary 6.6 and Definition 6.5; proof pp. 41–42 (PDF 42–43)

import Definitions.Def_MultiInterm_Compete_Efficiency

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MultiInterm.Compete

theorem corollary_6_6 (D : ValueDistribution) (hD : D.zeroMass = 0) (n : ℕ) (hn : 3 ≤ n)
    (r : Reserves) (s : BidderStrategy) (hs : Continuation D n r s) :
    ∃ τ : ℝ≥0, ThresholdOptimal D n s r τ ∧ ThresholdParticipation D s r τ := by sorry

end MultiInterm.Compete
