-- Prove2me | Theorems.Thm_IncrOpenAddr_NoTradeoff_lemma_4_5
-- name    : IncrOpenAddr.NoTradeoff.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:38:06.762855+00:00
-- url     : https://prove2.me/theorems/229fd52d-0783-4baf-98fa-99d62f07e41d
-- title:
--   Lemma 4.5 — a fixed level-ℓ node is expensive at a fixed time with probability O(2^{−20ℓ})
-- statement:
--   **Lemma 4.5.** For a sufficiently small constant $\eta>0$ there is a constant $C$ such that for every $n\ge8$, every list $xs$ of at most $n$ distinct keys inserted by the §4 algorithm, every node $V$ of the layout, at level $\ell$, and every time $t\le|xs|$,
--   $$\mathbb P\big(V\text{ is expensive after }t\text{ insertions}\big)\ \le\ C\,2^{-20\ell}.$$
--
--   Differences from the source:
--   - reading: η is a small constant, fixed by (6) η ≤ 1/(400(λ+1)^6) for a sufficiently large λ → ∃ η₀ > 0 such that the claim holds for every η ∈ (0, η₀]; reason: (6) with λ ≥ λ₀ is exactly η ≤ 1/(400(λ₀+1)^6); the claim is for the construction's fixed η, which may be any sufficiently small value
--   - reading: §2 assumes n a power of two; App. A.1 handles arbitrary n assuming n ≥ 8 'without loss of generality' → every n ≥ 8, with the App. A.1 layout (which for n a power of two is the §2 layout); reason: the paper's construction is only defined for n ≥ 8; smaller tables are a constant-size case of Theorem 1.1 only
--   - encoding: elements with fully random hashes L_i(x), g_i(x) → keys from an arbitrary finite linearly ordered type K; the law hashLaw K n makes all L_i(x) uniform on the leaves of T_i and all g_i(x) uniform on [0,1], all independent; the inserted keys are a duplicate-free list xs of length ≤ n; reason: only the hashes of the finitely many keys involved matter, so a finite key universe changes no instance; the order on K is the order used by the §4 node bits
--   - reading: O(2^{−20ℓ}) → ∃ C (after η, before n, the keys, V and t); reason: one constant for all instances
--   - reading: 'place x in an empty slot of U', 'a nonfull child', the slot order inside nodes left to the implementation (§4: every touched node keeps its bit) → the fixed bit-preserving implementation of Def_IncrOpenAddr_NoTradeoff_Algorithm (first empty slot, first two slots sorted increasingly; left child when U is off the path; step 3 takes the first candidate slot of V); reason: the paper leaves these choices free; the statement is made for one admissible implementation
-- source:
--   Farach-Colton, Krapivin, Kuszmaul, Incremental Open Addressing Has No Time-Space Tradeoff, arXiv:2611.04186 (manuscript sha256 9486c2b8…), p. 23 (PDF 24), Lemma 4.5

import Mathlib
import Definitions.Def_IncrOpenAddr_NoTradeoff_Layout
import Definitions.Def_IncrOpenAddr_NoTradeoff_HashModel
import Definitions.Def_IncrOpenAddr_NoTradeoff_Algorithm
import Definitions.Def_IncrOpenAddr_NoTradeoff_Analysis
open MeasureTheory

namespace IncrOpenAddr.NoTradeoff

theorem lemma_4_5 :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∃ C : ℝ, ∀ n : ℕ, 8 ≤ n → ∀ (K : Type) [Fintype K] [LinearOrder K] (xs : List K),
        xs.Nodup → xs.length ≤ n →
        ∀ V : Node, V.Valid n → ∀ t : ℕ, t ≤ xs.length →
          hashLaw K n {ω | ExpensiveAt n η ω xs V t} ≤
            ENNReal.ofReal (C / (2 : ℝ) ^ (20 * V.level)) := by sorry

end IncrOpenAddr.NoTradeoff
