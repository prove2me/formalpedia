-- Prove2me | Theorems.Thm_MultiInterm_Compete_lemma_6_4
-- name    : MultiInterm.Compete.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:43:31.129016+00:00
-- url     : https://prove2.me/theorems/e8b0ed79-3995-4f41-885b-7ff25cb3d4b6
-- title:
--   Lemma 6.4 — the highest eligible value wins each downstream auction
-- statement:
--   Let $n\ge3$ bidders have independent values with the atomless regular law $D$ on $[0,\bar v]$, where $\bar v$ may be infinite. Fix downstream reserves $r=(r_A,r_B)$ and a symmetric continuation Bayes–Nash equilibrium $s$ in weakly undominated strategies, with four strictly increasing mode-specific bid functions. Both downstream auctions are second-price with their stated reserves; upstream is second-price with reserve zero and own-bid merging. Deviations and attachments are unrestricted.
--
--   Almost surely, each downstream auction has no winner if no bid meets its reserve; otherwise its winner $i$ is a highest-valued bidder among those whose submitted bids meet the reserve:
--   $$v_j\le v_i\quad\text{for every bidder }j\text{ with }b_j^\theta\ge r_\theta.$$
--   This orders outcomes across the single-homing and multi-homing modes, beyond the assumed within-mode bid monotonicity.
--
--   Differences from the source:
--   - encoding: nonnegative real values and reserves; bidders 1 through n; intermediaries A and B → nonnegative-real carriers, Fin n bidders, and Bool intermediaries (false=A, true=B); reason: these are relabelings of the same spaces; the support endpoint may still be infinite
--   - encoding: finite bundles of own upstream bids and uniform random tie-breaking → one optional attachment per downstream bid, own-bid maximum merging, and exact finite outcome weights; reason: footnote 4 and §5.2.1 identify the effective bundle with its maximum; absence and zero remain distinct
--   - encoding: expectations with potentially unbounded values and payments → nonnegative integrals for revenues and finite interim benefit minus extended expected payment for utility; reason: preserves infinite expectations and unrestricted deviations without assuming a finite mean or integrable payments
--   - reading: four strictly increasing bid functions with possibly randomized participation → arbitrary measurable mixtures over abstention, two single-homing modes and multi-homing, with increasing functions on the value support; reason: the brief and §3.1 distinguish mode-specific bids from participation; the hypothesis imposes no restriction on attachments
--   - encoding: atomless regular D on [0, v̄] → the referenced regular continuous component, full interval support, and zeroMass=0; reason: this specifies the same density and virtual-value convention with no finite-mean condition
--   - generalization: single-homers bid zero in the other downstream auction (p. 10) → a single-homer's other auction receives a zero bid or no bid; reason: at a positive reserve a zero bid does not meet it, so both give the same outcome; at a zero reserve the source notes bidding zero dominates abstaining (p. 10); the source's zero-bid strategies are a special case
-- source:
--   Ganesh, Moallemi, Weinberg, On the Power and Limitations of Multiple Intermediaries for Single-Item Auctions, STOC 2027 submission (sha256 bdc0557e98c014301646135a34b1532361d0f6133aa7832c59b68394fa2a81dc), p. 16 (PDF 17), Lemma 6.4; proof pp. 38–41 (PDF 39–42)

import Definitions.Def_MultiInterm_Compete_Efficiency

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MultiInterm.Compete

theorem lemma_6_4 (D : ValueDistribution) (hD : D.zeroMass = 0) (n : ℕ) (hn : 3 ≤ n)
    (r : Reserves) (s : BidderStrategy) (hs : Continuation D n r s) :
    AlmostSurely D n s r fun z w _ => ∀ θ,
      ((∀ i, ¬ Meets (r θ) (downstreamBids z θ i)) ∧ w θ = none) ∨
      ∃ i, w θ = some i ∧ Meets (r θ) (downstreamBids z θ i) ∧
        ∀ j, Meets (r θ) (downstreamBids z θ j) → (z j).1 ≤ (z i).1 := by sorry

end MultiInterm.Compete
