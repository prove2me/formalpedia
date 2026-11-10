-- Prove2me | Theorems.Thm_IncrOpenAddr_NoTradeoff_lemma_4_4
-- name    : IncrOpenAddr.NoTradeoff.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:38:24.816213+00:00
-- url     : https://prove2.me/theorems/88c20b0b-cbc9-4f8e-a838-9eb99d108335
-- title:
--   Lemma 4.4 — queries are correct: a present element is never reported absent
-- statement:
--   **Lemma 4.4 (Correctness).** For a sufficiently small constant $\eta>0$, every $n\ge8$, every outcome of the hashes and every list $xs$ of at most $n$ distinct keys inserted by the §4 algorithm, at every time $t\le|xs|$ every key $z$ in the table lies in a node that the query for $z$ waits for (with the true $I(z)$). Since the query reports $z$ absent only after reading every node it waits for, and reports $z$ as soon as it reads it, a query never reports a present element as absent.
--
--   Differences from the source:
--   - reading: η is a small constant, fixed by (6) η ≤ 1/(400(λ+1)^6) for a sufficiently large λ → ∃ η₀ > 0 such that the claim holds for every η ∈ (0, η₀]; reason: (6) with λ ≥ λ₀ is exactly η ≤ 1/(400(λ₀+1)^6); the claim is for the construction's fixed η, which may be any sufficiently small value
--   - reading: §2 assumes n a power of two; App. A.1 handles arbitrary n assuming n ≥ 8 'without loss of generality' → every n ≥ 8, with the App. A.1 layout (which for n a power of two is the §2 layout); reason: the paper's construction is only defined for n ≥ 8; smaller tables are a constant-size case of Theorem 1.1 only
--   - reading: a query never reports a present element as absent → every node holding z is one the query for z waits for (Safe with I = I(z)); reason: §4 defines 'waits for v' as 'does not report x absent until v has been read', and the query reports x as soon as it sees it; so the two are equivalent
--   - encoding: elements with random hashes → an arbitrary outcome ω : Outcome K n; reason: the claim is deterministic
--   - reading: 'place x in an empty slot of U', 'a nonfull child', the slot order inside nodes left to the implementation (§4: every touched node keeps its bit) → the fixed bit-preserving implementation of Def_IncrOpenAddr_NoTradeoff_Algorithm (first empty slot, first two slots sorted increasingly; left child when U is off the path; step 3 takes the first candidate slot of V); reason: the paper leaves these choices free; the statement is made for one admissible implementation
-- source:
--   Farach-Colton, Krapivin, Kuszmaul, Incremental Open Addressing Has No Time-Space Tradeoff, arXiv:2611.04186 (manuscript sha256 9486c2b8…), p. 23 (PDF 24), Lemma 4.4

import Mathlib
import Definitions.Def_IncrOpenAddr_NoTradeoff_Layout
import Definitions.Def_IncrOpenAddr_NoTradeoff_HashModel
import Definitions.Def_IncrOpenAddr_NoTradeoff_Algorithm
import Definitions.Def_IncrOpenAddr_NoTradeoff_Analysis

namespace IncrOpenAddr.NoTradeoff

theorem lemma_4_4 :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ n : ℕ, 8 ≤ n → ∀ (K : Type) [LinearOrder K] (ω : Outcome K n) (xs : List K),
        xs.Nodup → xs.length ≤ n →
        ∀ t : ℕ, t ≤ xs.length → ∀ z : K,
          Safe n (tableAt .sec4 n η ω xs t) ω z (Iof n (tableAt .sec4 n η ω xs t) ω z) := by sorry

end IncrOpenAddr.NoTradeoff
