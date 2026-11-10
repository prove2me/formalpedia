-- Prove2me | Theorems.Thm_MultiInterm_Compete_lemma_6_3
-- name    : MultiInterm.Compete.lemma_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:43:11.924455+00:00
-- url     : https://prove2.me/theorems/861f9077-8089-4903-8247-93b65b92e10b
-- title:
--   Lemma 6.3 — positive bids at a zero reserve
-- statement:
--   Let $n\ge3$ bidders have independent values with the atomless regular law $D$ on $[0,\bar v]$, where $\bar v$ may be infinite. Fix downstream reserves $r=(r_A,r_B)$ and a symmetric continuation Bayes–Nash equilibrium $s$ in weakly undominated strategies, with four strictly increasing mode-specific bid functions. Both downstream auctions are second-price with their stated reserves; upstream is second-price with reserve zero and own-bid merging. Deviations and attachments are unrestricted.
--
--   If intermediary $\theta$ has reserve zero, then almost every positive-value type submits a strictly positive bid to $\theta$ with probability one. Equivalently, under the joint value and action draws,
--   $$\Pr[\text{every bidder of positive value bids positively at }\theta]=1.$$
--   This describes effective participation at zero reserves.
--
--   Differences from the source:
--   - encoding: nonnegative real values and reserves; bidders 1 through n; intermediaries A and B → nonnegative-real carriers, Fin n bidders, and Bool intermediaries (false=A, true=B); reason: these are relabelings of the same spaces; the support endpoint may still be infinite
--   - encoding: finite bundles of own upstream bids and uniform random tie-breaking → one optional attachment per downstream bid, own-bid maximum merging, and exact finite outcome weights; reason: footnote 4 and §5.2.1 identify the effective bundle with its maximum; absence and zero remain distinct
--   - encoding: expectations with potentially unbounded values and payments → nonnegative integrals for revenues and finite interim benefit minus extended expected payment for utility; reason: preserves infinite expectations and unrestricted deviations without assuming a finite mean or integrable payments
--   - reading: four strictly increasing bid functions with possibly randomized participation → arbitrary measurable mixtures over abstention, two single-homing modes and multi-homing, with increasing functions on the value support; reason: the brief and §3.1 distinguish mode-specific bids from participation; the hypothesis imposes no restriction on attachments
--   - encoding: atomless regular D on [0, v̄] → the referenced regular continuous component, full interval support, and zeroMass=0; reason: this specifies the same density and virtual-value convention with no finite-mean condition
--   - generalization: single-homers bid zero in the other downstream auction (p. 10) → a single-homer's other auction receives a zero bid or no bid; reason: at a positive reserve a zero bid does not meet it, so both give the same outcome; at a zero reserve the source notes bidding zero dominates abstaining (p. 10); the source's zero-bid strategies are a special case
-- source:
--   Ganesh, Moallemi, Weinberg, On the Power and Limitations of Multiple Intermediaries for Single-Item Auctions, STOC 2027 submission (sha256 bdc0557e98c014301646135a34b1532361d0f6133aa7832c59b68394fa2a81dc), p. 16 (PDF 17), Lemma 6.3; proof p. 38 (PDF 39)

import Definitions.Def_MultiInterm_Compete_Efficiency

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MultiInterm.Compete

theorem lemma_6_3 (D : ValueDistribution) (hD : D.zeroMass = 0) (n : ℕ) (hn : 3 ≤ n)
    (r : Reserves) (s : BidderStrategy) (hs : Continuation D n r s) (θ : Bool) (hr : r θ = 0) :
    ∀ᵐ v ∂D.law, 0 < v → ∀ᵐ a ∂s.kernel v,
      ∃ b q, a θ = some (b, q) ∧ 0 < b := by sorry

end MultiInterm.Compete
