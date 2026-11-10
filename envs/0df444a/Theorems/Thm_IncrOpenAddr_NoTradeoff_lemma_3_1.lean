-- Prove2me | Theorems.Thm_IncrOpenAddr_NoTradeoff_lemma_3_1
-- name    : IncrOpenAddr.NoTradeoff.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:38:26.659738+00:00
-- url     : https://prove2.me/theorems/344c61eb-c226-4d09-b0ec-6886d7ba3410
-- title:
--   Lemma 3.1 — a fixed element is evicted in epoch s ≥ 3 with probability O((3/4)^s)
-- statement:
--   **Lemma 3.1.** For a sufficiently small constant $\eta>0$ there is a constant $C$ such that for every $n\ge8$, every list $xs$ of at most $n$ distinct keys inserted by the §3 algorithm (with eviction), every key $x$ and every epoch $s\ge3$,
--   $$\mathbb P\big(x\text{ is evicted in epoch }s\big)\ \le\ C\,(3/4)^s,$$
--   where $x$ is evicted when an insertion of epoch $s$ finds $x$ in the first slot of its leaf $L_1(\cdot)$ and moves it out to be reinserted by the §2 algorithm.
--
--   Differences from the source:
--   - reading: η is a small constant, fixed by (6) η ≤ 1/(400(λ+1)^6) for a sufficiently large λ → ∃ η₀ > 0 such that the claim holds for every η ∈ (0, η₀]; reason: (6) with λ ≥ λ₀ is exactly η ≤ 1/(400(λ₀+1)^6); the claim is for the construction's fixed η, which may be any sufficiently small value
--   - reading: §2 assumes n a power of two; App. A.1 handles arbitrary n assuming n ≥ 8 'without loss of generality' → every n ≥ 8, with the App. A.1 layout (which for n a power of two is the §2 layout); reason: the paper's construction is only defined for n ≥ 8; smaller tables are a constant-size case of Theorem 1.1 only
--   - encoding: elements with fully random hashes L_i(x), g_i(x) → keys from an arbitrary finite linearly ordered type K; the law hashLaw K n makes all L_i(x) uniform on the leaves of T_i and all g_i(x) uniform on [0,1], all independent; the inserted keys are a duplicate-free list xs of length ≤ n; reason: only the hashes of the finitely many keys involved matter, so a finite key universe changes no instance; the order on K is the order used by the §4 node bits
--   - reading: O((3/4)^s) → ∃ C (after η, before n, the keys, x and s); reason: one constant for all instances
--   - reading: 'place x in an empty slot of U', 'a nonfull child', the slot order inside nodes left to the implementation (§4: every touched node keeps its bit) → the fixed bit-preserving implementation of Def_IncrOpenAddr_NoTradeoff_Algorithm (first empty slot, first two slots sorted increasingly; left child when U is off the path; step 3 takes the first candidate slot of V); reason: the paper leaves these choices free; the statement is made for one admissible implementation
-- source:
--   Farach-Colton, Krapivin, Kuszmaul, Incremental Open Addressing Has No Time-Space Tradeoff, arXiv:2611.04186 (manuscript sha256 9486c2b8…), p. 17 (PDF 18), Lemma 3.1

import Mathlib
import Definitions.Def_IncrOpenAddr_NoTradeoff_Layout
import Definitions.Def_IncrOpenAddr_NoTradeoff_HashModel
import Definitions.Def_IncrOpenAddr_NoTradeoff_Algorithm
import Definitions.Def_IncrOpenAddr_NoTradeoff_Analysis
open MeasureTheory

namespace IncrOpenAddr.NoTradeoff

theorem lemma_3_1 :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∃ C : ℝ, ∀ n : ℕ, 8 ≤ n → ∀ (K : Type) [Fintype K] [LinearOrder K] (xs : List K),
        xs.Nodup → xs.length ≤ n →
        ∀ (x : K) (s : ℕ), 3 ≤ s →
          hashLaw K n {ω | ∃ r ∈ recs .sec3 n η ω xs, r.epoch = s ∧ r.evicted = some x} ≤
            ENNReal.ofReal (C * (3 / 4 : ℝ) ^ s) := by sorry

end IncrOpenAddr.NoTradeoff
