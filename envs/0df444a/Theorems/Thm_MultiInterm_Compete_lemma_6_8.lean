-- Prove2me | Theorems.Thm_MultiInterm_Compete_lemma_6_8
-- name    : MultiInterm.Compete.lemma_6_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:43:37.248874+00:00
-- url     : https://prove2.me/theorems/3555fab8-07fa-49dc-b3cd-b18eaafd6dbd
-- title:
--   Lemma 6.8 — profitable undercutting reserves, including an atom at zero
-- statement:
--   Let $n\ge3$ bidders have independent values with the regular law $D$, atomless away from a possible atom at zero, on $[0,\bar v]$, where $\bar v$ may be infinite. Fix downstream reserves $r=(r_A,r_B)$ and a symmetric continuation Bayes–Nash equilibrium $s$ in weakly undominated strategies, with four strictly increasing mode-specific bid functions. Both downstream auctions are second-price with their stated reserves; upstream is second-price with reserve zero and own-bid merging. Deviations and attachments are unrestricted.
--
--   Suppose the continuation equilibrium is surplus-optimal up to $0<\tau<\bar v$. There are reserves $s_A,s_B\in(0,\tau)$ such that
--   $$s_A<g(r_B),\qquad s_B<g(r_A),\qquad R(s_A)+R(s_B)>R(\tau).$$
--   Here $g(x)=xF(x)^{n-1}$ and $R$ is the reserve-revenue formula. This includes the atom-at-zero extension expressly stated immediately after Lemma 6.8. It supplies the two simultaneous revenue comparisons used for reserve competition.
--
--   Differences from the source:
--   - encoding: nonnegative real values and reserves; bidders 1 through n; intermediaries A and B → nonnegative-real carriers, Fin n bidders, and Bool intermediaries (false=A, true=B); reason: these are relabelings of the same spaces; the support endpoint may still be infinite
--   - encoding: finite bundles of own upstream bids and uniform random tie-breaking → one optional attachment per downstream bid, own-bid maximum merging, and exact finite outcome weights; reason: footnote 4 and §5.2.1 identify the effective bundle with its maximum; absence and zero remain distinct
--   - encoding: expectations with potentially unbounded values and payments → nonnegative integrals for revenues and finite interim benefit minus extended expected payment for utility; reason: preserves infinite expectations and unrestricted deviations without assuming a finite mean or integrable payments
--   - reading: four strictly increasing bid functions with possibly randomized participation → arbitrary measurable mixtures over abstention, two single-homing modes and multi-homing, with increasing functions on the value support; reason: the brief and §3.1 distinguish mode-specific bids from participation; the hypothesis imposes no restriction on attachments
--   - encoding: the density formula for R with integration from τ to v̄ → the same nonnegative integrand integrated against D over (τ,∞), valued in extended nonnegative reals; reason: dD=f(v)dv away from zero and D vanishes beyond its support; the omitted zero endpoint contributes zero
--   - generalization: the regular value distribution may have an atom at zero but is atomless elsewhere → D=pδ₀+(1-p)ν with 0≤p<1 and ν an atomless regular full-support component; reason: the sentence following Lemma 6.8 (p. 17, part of the milestone verbatim) extends the lemma to this class; normalizing the positive part preserves virtual values because the survival function and density share the factor 1-p; p=0 is the printed lemma
--   - generalization: single-homers bid zero in the other downstream auction (p. 10) → a single-homer's other auction receives a zero bid or no bid; reason: at a positive reserve a zero bid does not meet it, so both give the same outcome; at a zero reserve the source notes bidding zero dominates abstaining (p. 10); the source's zero-bid strategies are a special case
-- source:
--   Ganesh, Moallemi, Weinberg, On the Power and Limitations of Multiple Intermediaries for Single-Item Auctions, STOC 2027 submission (sha256 bdc0557e98c014301646135a34b1532361d0f6133aa7832c59b68394fa2a81dc), p. 17 (PDF 18), Lemma 6.8 and following extension; proof pp. 43–44 (PDF 44–45)

import Definitions.Def_MultiInterm_Compete_Efficiency

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MultiInterm.Compete

theorem lemma_6_8 (D : ValueDistribution) (n : ℕ) (hn : 3 ≤ n)
    (r : Reserves) (s : BidderStrategy) (hs : Continuation D n r s) (τ : ℝ≥0) (hτ : 0 < τ)
    (hτv : (τ : ℝ≥0∞) < D.upper) (ha : ThresholdOptimal D n s r τ) :
    ∃ sA sB : ℝ≥0, (0 < sA ∧ sA < τ) ∧ (0 < sB ∧ sB < τ) ∧
      sA < g D n (r true) ∧ sB < g D n (r false) ∧
      R D n τ < R D n sA + R D n sB := by sorry

end MultiInterm.Compete
