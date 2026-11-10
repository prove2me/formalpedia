-- Prove2me | Theorems.Thm_MultiInterm_Compete_theorem_6_2
-- name    : MultiInterm.Compete.theorem_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:43:48.416494+00:00
-- url     : https://prove2.me/theorems/d5f5be52-5e49-4e33-8316-25f126bbf052
-- title:
--   Theorem 6.2 — competition drives both downstream reserves to zero
-- statement:
--   Let $n\ge3$ bidders have independent values drawn from an atomless regular distribution $D$ with support $[0,\bar v]$, where $\bar v$ may be infinite. Two intermediaries choose deterministic nonnegative reserves and run downstream second-price auctions. The seller runs an upstream second-price auction with reserve zero, merging bids identified as belonging to the same bidder.
--
--   In every symmetric perfect Bayesian equilibrium in weakly undominated bidder strategies whose four mode-specific bid functions are strictly increasing after every reserve pair, including off-path pairs,
--   $$(r_A,r_B)=(0,0).$$
--   Almost surely the highest-valued bidder wins both downstream auctions, receives the item upstream, and pays zero upstream. The equilibrium is also downstream efficient and surplus-optimal: its slot allocation maximizes total upstream utility, and the highest-valued bidder receives the item almost surely.
--
--   Bidder optimality and weak undominance permit every measurable mixed deviation with arbitrary bids and attachments. Intermediary optimality compares all nonnegative unilateral reserve deviations, using the specified continuation at each deviated pair. No existence of such an equilibrium is asserted. This is the paper's characterization of competing-intermediary equilibria.
--
--   Differences from the source:
--   - encoding: nonnegative real values and reserves; bidders 1 through n; intermediaries A and B → nonnegative-real carriers, Fin n bidders, and Bool intermediaries (false=A, true=B); reason: these are relabelings of the same spaces; the support endpoint may still be infinite
--   - encoding: finite bundles of own upstream bids and uniform random tie-breaking → one optional attachment per downstream bid, own-bid maximum merging, and exact finite outcome weights; reason: footnote 4 and §5.2.1 identify the effective bundle with its maximum; absence and zero remain distinct
--   - encoding: expectations with potentially unbounded values and payments → nonnegative integrals for revenues and finite interim benefit minus extended expected payment for utility; reason: preserves infinite expectations and unrestricted deviations without assuming a finite mean or integrable payments
--   - reading: four strictly increasing bid functions with possibly randomized participation → arbitrary measurable mixtures over abstention, two single-homing modes and multi-homing, with increasing functions on the value support; reason: the brief and §3.1 distinguish mode-specific bids from participation; the hypothesis imposes no restriction on attachments
--   - encoding: atomless regular D on [0, v̄] → the referenced regular continuous component, full interval support, and zeroMass=0; reason: this specifies the same density and virtual-value convention with no finite-mean condition
--   - encoding: perfect Bayesian equilibrium with beliefs equal to the prior → BNE and weak undominance after every reserve pair, four-function increase at every pair, and pure reserve best responses; reason: the only bidder decision follows the publicly observed reserves; beliefs are fixed by §3.1, and mixed reserve deviations cannot outperform all pure ones
--   - reading: surplus optimal → almost-sure allocation to a highest-valued bidder; reason: the brief requires the allocation reading of Definition 6.5, which also covers infinite means
--   - encoding: downstream winners maximize the sum of upstream utilities → their conditional upstream utility is maximal over all feasible two-slot assignments and attached bids; reason: this spells out the feasible allocations in §5.1; the upstream zero-reserve auction can attain the highest value by assigning both slots to that bidder
--   - generalization: single-homers bid zero in the other downstream auction (p. 10) → a single-homer's other auction receives a zero bid or no bid; reason: at a positive reserve a zero bid does not meet it, so both give the same outcome; at a zero reserve the source notes bidding zero dominates abstaining (p. 10); the source's zero-bid strategies are a special case
-- source:
--   Ganesh, Moallemi, Weinberg, On the Power and Limitations of Multiple Intermediaries for Single-Item Auctions, STOC 2027 submission (sha256 bdc0557e98c014301646135a34b1532361d0f6133aa7832c59b68394fa2a81dc), p. 15 (PDF 16), Theorem 6.2; proof pp. 16–17 (PDF 17–18)

import Definitions.Def_MultiInterm_Compete_Efficiency

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MultiInterm.Compete

theorem theorem_6_2 (D : ValueDistribution) (hD : D.zeroMass = 0) (n : ℕ) (hn : 3 ≤ n)
    (σ : SymmetricStrategy) (r : Reserves) (heq : Equilibrium D n σ r) :
    r = (fun _ => 0) ∧
    AlmostSurely D n (σ r) r (fun z w u => ∃ i, Highest z i ∧
      w false = some i ∧ w true = some i ∧ u = some i ∧ upstreamPayment z w u i = 0) ∧
    DownstreamEfficient D n (σ r) r ∧ SurplusOptimal D n (σ r) r := by sorry

end MultiInterm.Compete
