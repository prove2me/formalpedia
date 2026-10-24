-- Prove2me | Theorems.Thm_InterdepSOS_RSV_theorem_4_1
-- name    : InterdepSOS.RSV.theorem_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:29.044733+00:00
-- url     : https://prove2.me/theorems/c574f08f-3dd9-4234-afdf-ed837289550d
-- title:
--   Theorem 4.1, p. 14 — RS-V is universally ex-post IC-IR and a 2(d+1)-approximation
-- statement:
--   Consider a downward-closed family $\mathcal I$ of feasible served sets and nonnegative valuations that are weakly increasing in every signal, strictly increasing in each agent's own signal, and $d$-SOS. For every rule that selects a feasible maximizer of the Random Sampling Vickrey proxy weights from the candidate set of each partition, each deterministic partition component admits a payment rule that makes it ex-post incentive compatible and individually rational. Moreover, for every true signal profile $s$ and feasible comparator $S\in\mathcal I$,
--
--   $$
--   \sum_{i\in S}v_i(s)\le 2(d+1)\,\mathbb E_B\left[\sum_{i\in x_B(s)}v_i(s)\right].
--   $$
--
--   Thus RS-V is universally ex-post IC-IR and achieves a $2(d+1)$ welfare approximation. The SOS case $d=1$ gives the stated factor $4$.
--
--   **Formalization Note** Signals include zero; payments are functions of reported profiles, and the welfare average uses true valuations at the truthful profile. No separate bound $d\ge1$ is assumed: strict increase in an agent's own signal combined with the $d$-SOS inequality entails it when there is an agent. The selector hypothesis makes feasibility and maximization explicit.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), p. 14, Theorem 4.1

import Mathlib
import Definitions.Def_InterdepSOS_RSV_Setting

namespace InterdepSOS.RSV

theorem theorem_4_1 {n : ℕ} (I : Set (Finset (Fin n)))
    (hI : IsDownwardClosed I) (v : Valuation n) (hv : IsValuation v)
    (d : ℝ) (hd : ∀ i, IsDSOS d (v i))
    (sel : Finset (Fin n) → Allocation n) (hsel : IsRSVSelector I v sel) :
    (∀ B, ∃ p : Payment n,
      IsExPostIC v (sel B) p ∧ IsExPostIR v (sel B) p) ∧
    ∀ s, ∀ S ∈ I,
      (∑ i ∈ S, v i s) ≤
        2 * (d + 1) * avgB (fun B => ∑ i ∈ sel B s, v i s) := by sorry

end InterdepSOS.RSV
