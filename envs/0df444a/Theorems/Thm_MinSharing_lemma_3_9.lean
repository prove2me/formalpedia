-- Prove2me | Theorems.Thm_MinSharing_lemma_3_9
-- name    : MinSharing.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:02.962965+00:00
-- url     : https://prove2.me/theorems/2f870fcc-4259-4213-b58a-bc0f8d81b935
-- title:
--   Lemma 3.9 — from $\mathcal G_{v^k}$ to $\mathcal G_{v^{k+1}}$: bound (3.2) and enumeration
-- statement:
--   Let $v$ be a real valuation matrix with $n\ge3$ agents and $m\ge1$ objects, let $2\le k\le n-1$, and let $v^k$ be the valuation of the first $k$ agents. With $D_v$ the degeneracy of the whole matrix $v$:
--
--   1. the numbers of fPO graphs satisfy
--   $$|\mathcal G_{v^{k+1}}|\le|\mathcal G_{v^k}|\cdot3^{(D_v+1)k}\cdot m^k ; \tag{3.2}$$
--   2. for each $n\ge3$ there are a real-RAM program $R$, a report position $p$ and a constant $K>0$ such that, for all such $k$, $m$, $v$, when the input memory holds $v$, $k$ and a duplicate-free list of exactly the graphs of $\mathcal G_{v^k}$, the program enumerates $\mathcal G_{v^{k+1}}$ within
--   $$K\cdot|\mathcal G_{v^k}|\cdot3^{D_v\cdot k}\cdot m^{2+k}$$
--   steps.
--
--   Applied for $k=2,\dots,n-1$ starting from Lemma 3.8, this gives Proposition 3.7 and the bound (3.1).
--
--   Differences from the source:
--   - encoding: every count and step bound for m objects → stated for m ≥ 1; reason: the paper writes [m] = {1,…,m}; at m = 0 the set G_v = {∅} has one element while the printed bounds are 0
--   - encoding: D_v → the integer degeneracy v, which can be −1, with 3^(…D_v) a real power with integer exponent; reason: D_v + 1 counts objects and can be 0 (e.g. n = 2, m = 1, v = (1; 0)); no truncation at 0
--   - reading: G_v can be enumerated using O(f) operations → EnumeratesWithin: R halts within K·f steps; whenever the program counter is at a fixed report position p before halting, the graph region of memory holds a graph of the set, and every graph of the set is held there at some such step; reason: writing every graph out in full would make Lemma 3.8(b) false (2m + 1 graphs with Θ(m) edges each for non-degenerate pure goods); the proof says consecutive graphs differ only in the objects of A=(t) and A=(t′), p.17
--   - reading: enumerated using O(|G_{v^k}|·3^{D_v·k}·m^{2+k}) operations → number of executed instructions of one program of the published real RAM (SmaleNinth.RAMProgram, unit cost, exact real arithmetic) bounded by K times the expression, with the output correct; reason: the paper counts arithmetic operations and comparisons on real numbers (multiplicative Bellman–Ford, App. A p.31; constant-size LPs, p.14)
--   - reading: O(·) in Lemma 3.9(b) → the constant K may depend on n (chosen after n, before k, m, v); reason: the proof bounds the fPO test of each candidate by O(m²) and the per-graph work by O(m·3^{D_v})^k, constants that depend on k ≤ n − 1; the lemma serves Proposition 3.7, where n is fixed
--   - reading: G_{v^k} is given as the input → the input memory holds a duplicate-free list whose elements are exactly the graphs of G_{v^k}, each as 0/1 entries; reason: a list is how a set of graphs is given to an algorithm
--   - encoding: agents [n] = {1,…,n}, objects [m] = {1,…,m} → Fin n, Fin m (paper index = Lean index + 1); reason: Lean convention; same instances
-- source:
--   Sandomirskiy, Segal-Halevi, Efficient Fair Division with Minimal Sharing, arXiv:1908.01669v3, Lemma 3.9, p.17 (proof pp.17–18)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_MinSharing_Setting
import Definitions.Def_MinSharing_RAMInterface

set_option autoImplicit false

namespace MinSharing

open SmaleNinth

/-- **Lemma 3.9** (Sandomirskiy, Segal-Halevi, arXiv:1908.01669v3, p.17). For a valuation `v`
with `n ≥ 3` agents and `k` such that `2 ≤ k ≤ n − 1`:
(a) `|G_{v^{k+1}}| ≤ |G_{v^k}| · 3^{(D_v+1)k} · m^k` (3.2);
(b) all the graphs in `G_{v^{k+1}}` can be enumerated using `O(|G_{v^k}| · 3^{D_v·k} · m^{2+k})`
operations if `G_{v^k}` is given as the input.

**Formalization Note** `vᵏ` is `subInstance v k`, the first `k` agents. `D_v` is the degeneracy of
the whole `n`-agent matrix `v` (an integer, possibly `−1`); `m ≥ 1`. (b): for each `n ≥ 3` there are
a program `R` of the published real RAM, a report position `p` and a constant `K > 0` (depending on
`n` only), chosen before `k`, `m`, `v`. The input memory `graphListMem v k Gs` holds `v`, `k` and a
duplicate-free list `Gs` whose elements are exactly the graphs of `G_{v^k}`; `R` halts within
`K · |G_{v^k}| · 3^{D_v·k} · m^{2+k}` steps and enumerates `G_{v^{k+1}}` in the sense of
`EnumeratesWithin` (graphs on the agent rows `0, …, k`). -/
theorem lemma_3_9 (n : ℕ) (hn : 3 ≤ n) :
    (∀ k : ℕ, 2 ≤ k → k ≤ n - 1 → ∀ m : ℕ, 1 ≤ m → ∀ v : Fin n → Fin m → ℝ,
      ((fpoGraphs (subInstance v (k + 1))).ncard : ℝ) ≤
        (fpoGraphs (subInstance v k)).ncard * (3 : ℝ) ^ ((degeneracy v + 1) * (k : ℤ)) *
          (m : ℝ) ^ k) ∧
    ∃ R : RAMProgram, ∃ p : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ k : ℕ, 2 ≤ k → k ≤ n - 1 → ∀ m : ℕ, 1 ≤ m → ∀ v : Fin n → Fin m → ℝ,
        ∀ Gs : List (Finset (Fin k × Fin m)), Gs.Nodup →
          (∀ G, G ∈ Gs ↔ G ∈ fpoGraphs (subInstance v k)) →
          EnumeratesWithin n m (k + 1) R p (graphListMem v k Gs)
            (fpoGraphs (subInstance v (k + 1)))
            (K * (fpoGraphs (subInstance v k)).ncard * (3 : ℝ) ^ (degeneracy v * (k : ℤ)) *
              (m : ℝ) ^ (2 + k)) := by sorry

end MinSharing
