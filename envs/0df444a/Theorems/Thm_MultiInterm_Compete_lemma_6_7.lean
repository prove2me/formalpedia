-- Prove2me | Theorems.Thm_MultiInterm_Compete_lemma_6_7
-- name    : MultiInterm.Compete.lemma_6_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:43:34.829192+00:00
-- url     : https://prove2.me/theorems/3abc2a4f-6eee-4bde-9587-7beb84bf0a1e
-- title:
--   Lemma 6.7 — a sufficiently low reserve captures the market
-- statement:
--   Let $n\ge3$ bidders have independent values with the atomless regular law $D$ on $[0,\bar v]$, where $\bar v$ may be infinite. Fix downstream reserves $r=(r_A,r_B)$ and a symmetric continuation Bayes–Nash equilibrium $s$ in weakly undominated strategies, with four strictly increasing mode-specific bid functions. Both downstream auctions are second-price with their stated reserves; upstream is second-price with reserve zero and own-bid merging. Deviations and attachments are unrestricted.
--
--   Write $r>0$ for the other intermediary's reserve and let $g(x)=xF(x)^{n-1}$, where $F$ is the CDF. If intermediary $\theta$ chooses reserve $s$ satisfying
--   $$0\le s<\min\{g(r),\bar v\},$$
--   then $\theta$ is relevant and the other intermediary is irrelevant. The composite outcome implements an ordinary second-price auction with reserve $s$, with zero upstream payments, and intermediary $\theta$ earns expected revenue $R(s)$. Here $R$ is the displayed reserve-revenue formula of Definition 6.5. The assertion applies to every continuation equilibrium satisfying the stated assumptions at that pair of reserves.
--
--   Differences from the source:
--   - encoding: nonnegative real values and reserves; bidders 1 through n; intermediaries A and B → nonnegative-real carriers, Fin n bidders, and Bool intermediaries (false=A, true=B); reason: these are relabelings of the same spaces; the support endpoint may still be infinite
--   - encoding: finite bundles of own upstream bids and uniform random tie-breaking → one optional attachment per downstream bid, own-bid maximum merging, and exact finite outcome weights; reason: footnote 4 and §5.2.1 identify the effective bundle with its maximum; absence and zero remain distinct
--   - encoding: expectations with potentially unbounded values and payments → nonnegative integrals for revenues and finite interim benefit minus extended expected payment for utility; reason: preserves infinite expectations and unrestricted deviations without assuming a finite mean or integrable payments
--   - reading: four strictly increasing bid functions with possibly randomized participation → arbitrary measurable mixtures over abstention, two single-homing modes and multi-homing, with increasing functions on the value support; reason: the brief and §3.1 distinguish mode-specific bids from participation; the hypothesis imposes no restriction on attachments
--   - encoding: atomless regular D on [0, v̄] → the referenced regular continuous component, full interval support, and zeroMass=0; reason: this specifies the same density and virtual-value convention with no finite-mean condition
--   - encoding: the density formula for R with integration from τ to v̄ → the same nonnegative integrand integrated against D over (τ,∞), valued in extended nonnegative reals; reason: dD=f(v)dv away from zero and D vanishes beyond its support; the omitted zero endpoint contributes zero
--   - encoding: implements an ordinary second-price auction with reserve s → almost-sure equality of winner and individual payments to the truthful second-price outcome, plus zero upstream payments; reason: implementation specifies outcomes, without adding truthful bidding as a hypothesis
--   - generalization: single-homers bid zero in the other downstream auction (p. 10) → a single-homer's other auction receives a zero bid or no bid; reason: at a positive reserve a zero bid does not meet it, so both give the same outcome; at a zero reserve the source notes bidding zero dominates abstaining (p. 10); the source's zero-bid strategies are a special case
-- source:
--   Ganesh, Moallemi, Weinberg, On the Power and Limitations of Multiple Intermediaries for Single-Item Auctions, STOC 2027 submission (sha256 bdc0557e98c014301646135a34b1532361d0f6133aa7832c59b68394fa2a81dc), p. 17 (PDF 18), Lemma 6.7; proof pp. 42–43 (PDF 43–44)

import Definitions.Def_MultiInterm_Compete_Efficiency

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MultiInterm.Compete

theorem lemma_6_7 (D : ValueDistribution) (hD : D.zeroMass = 0) (n : ℕ) (hn : 3 ≤ n)
    (r : Reserves) (s : BidderStrategy) (hs : Continuation D n r s) (θ : Bool) (hr : 0 < r (!θ))
    (hsr : r θ < g D n (r (!θ))) (hsv : (r θ : ℝ≥0∞) < D.upper) :
    Relevant D n s r θ ∧ ¬ Relevant D n s r (!θ) ∧
    OrdinarySecondPrice D n s r θ ∧ revenue D n s r θ = R D n (r θ) := by sorry

end MultiInterm.Compete
