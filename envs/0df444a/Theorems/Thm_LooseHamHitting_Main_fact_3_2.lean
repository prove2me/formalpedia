-- Prove2me | Theorems.Thm_LooseHamHitting_Main_fact_3_2
-- name    : LooseHamHitting.Main.fact_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:17:52.667136+00:00
-- url     : https://prove2.me/theorems/5b82b48b-4257-4d41-92a8-2af036676f99
-- title:
--   Fact 3.2 — a (G, M)-respecting mixed Hamilton cycle with k triples has k private and k + s intersection vertices, and n = 2k + s
-- statement:
--   Let $G$ be a 3-graph on a vertex set $V$ with $|V|=n$, let $M$ be a matching of $s=|M|$ pairs on $V$, and let $C$ be a $(G,M)$-respecting mixed Hamilton cycle with $k$ triples. Then:
--
--   1. every $M$-saturated vertex lies in exactly one triple of $C$ and exactly one pair of $M$;
--   2. $C$ has $k$ private vertices and $k+s$ intersection vertices, of which $2s$ are $M$-saturated and $k-s$ are $M$-unsaturated;
--   3. $$n=2k+s,\qquad k=\frac{n-s}2,\qquad n+s\ \text{even}.$$
--
--   This bookkeeping fixes the number of triples of every counted cycle and is used throughout the counting.
--
--   Differences from the source:
--   - encoding: k − s M-unsaturated intersection vertices → the count as an integer equals (k : ℤ) − s; reason: avoids truncated natural subtraction; same statement
-- source:
--   León, Liu, Hitting time for loose Hamilton cycles in the random hypergraph process, arXiv:2610.29894v1, p. 8, Fact 3.2

import Mathlib
import Definitions.Def_LooseHamHitting_Main_Hypergraph

set_option autoImplicit false

open Classical

namespace LooseHamHitting.Main

/-- Fact 3.2: structure of a `(G, M)`-respecting mixed Hamilton cycle with `k` triples. -/
theorem fact_3_2 {β : Type*} (V : Finset β) (G M C : Finset (Finset β)) (n s k : ℕ)
    (hG : IsThreeGraph V G) (hM : IsMatching V M) (hC : IsMixedHamCycle V G M C)
    (hn : V.card = n) (hs : M.card = s) (hk : (C.filter (fun f => f.card = 3)).card = k) :
    (∀ v ∈ matchedVerts M, (C.filter (fun f => f.card = 3 ∧ v ∈ f)).card = 1 ∧
        (M.filter (fun p => v ∈ p)).card = 1) ∧
      ((privateVerts V C).card = k ∧ (intersectionVerts V C).card = k + s ∧
        (intersectionVerts V C ∩ matchedVerts M).card = 2 * s ∧
        ((intersectionVerts V C \ matchedVerts M).card : ℤ) = (k : ℤ) - s) ∧
      (n = 2 * k + s ∧ k = (n - s) / 2 ∧ Even (n + s)) := by sorry

end LooseHamHitting.Main
