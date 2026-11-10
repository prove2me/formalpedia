-- Prove2me | Theorems.Thm_IncrOpenAddr_NoTradeoff_eq_3
-- name    : IncrOpenAddr.NoTradeoff.eq_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:35:40.75743+00:00
-- url     : https://prove2.me/theorems/a5301363-3254-49c4-bb6a-7275e8b7cbba
-- title:
--   §2.2, Eq. (3) — the merged probe schedule reaches the k-th probe of T_i's local list within the first 16ik² probes
-- statement:
--   **Eq. (3) (§2.2, realized by the schedule of App. A.2).** For every table size $n\ge8$, every assignment of home leaves to the trees, every tree index $1\le i\le\alpha$ and every position $1\le k\le$ (length of $T_i$'s local list), the event "the $k$-th probe of $T_i$'s local list" occurs among the first $16ik^2$ probes of the merged query probe sequence:
--   $$\exists\,R,\ p<16\,i\,k^2:\quad \text{the }p\text{-th probe (from }0\text{) of the first }R\text{ rounds is the }k\text{-th probe of }T_i\text{'s local list}.$$
--
--   The merged sequence is the round-robin schedule of App. A.2 (round $r$, groups $a=0,\dots,r$, trees $T_{2^a},\dots,T_{2^{a+1}-1}$, prefixes of length $2^{\lfloor(r-a)/2\rfloor}$). It is the bridge from where an element sits in a tree to how many probes a query spends to find it.
--
--   Differences from the source:
--   - reading: §2 assumes n a power of two; App. A.1 handles arbitrary n assuming n ≥ 8 'without loss of generality' → every n ≥ 8, with the App. A.1 layout (which for n a power of two is the §2 layout); reason: the paper's construction is only defined for n ≥ 8; smaller tables are a constant-size case of Theorem 1.1 only
--   - reading: 'these local lists are merged into one sequence … such that' (3) holds; App. A.2 gives the schedule → the claim for the App. A.2 schedule; a visit reads the whole local list when it is shorter than its prefix length; reason: (3) is proved in App. A.2 for that schedule; the paper does not say what a visit does past the end of a local list
--   - encoding: the probe sequence of an element u → the sequence of probe events (tree, position) for an arbitrary leaf assignment leaf : ℕ → ℕ; the events do not depend on the leaves; reason: (3) is a statement about positions in the schedule
-- source:
--   Farach-Colton, Krapivin, Kuszmaul, Incremental Open Addressing Has No Time-Space Tradeoff, arXiv:2611.04186 (manuscript sha256 9486c2b8…), p. 10 (PDF 11), §2.2 Eq. (3); schedule and proof p. 35 (PDF 36), App. A.2

import Mathlib
import Definitions.Def_IncrOpenAddr_NoTradeoff_Layout

namespace IncrOpenAddr.NoTradeoff

theorem eq_3 :
    ∀ n : ℕ, 8 ≤ n → ∀ (leaf : ℕ → ℕ) (i k : ℕ), 1 ≤ i → i ≤ numTrees n → 1 ≤ k →
      k ≤ (localList n i (leaf i)).length →
      ∃ R p : ℕ, p < 16 * i * k ^ 2 ∧ (scheduleEvents n leaf R)[p]? = some (some (i, k)) := by sorry

end IncrOpenAddr.NoTradeoff
