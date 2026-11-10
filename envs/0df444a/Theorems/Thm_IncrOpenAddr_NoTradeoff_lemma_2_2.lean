-- Prove2me | Theorems.Thm_IncrOpenAddr_NoTradeoff_lemma_2_2
-- name    : IncrOpenAddr.NoTradeoff.lemma_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:38:14.128246+00:00
-- url     : https://prove2.me/theorems/ba0bd7d5-10aa-4451-82b1-e758d84533d4
-- title:
--   Lemma 2.2 — insertions never fail: T_i holds exactly ⌊(1−η)|T_i|⌋ current-array elements at t_i and is full at t_{i+1}
-- statement:
--   **Lemma 2.2 (Insertions never fail).** For a sufficiently small constant $\eta>0$, every $n\ge8$, every outcome $\omega$ of the hashes and every list $xs$ of at most $n$ distinct keys, the §2 algorithm inserting $xs$ in order:
--
--   1. never fails: every insertion places its element;
--   2. for every tree $T_i$ with $i<\alpha$, if $t_i\le|xs|$, then after $t_i$ insertions $T_i$ holds exactly $\lfloor(1-\eta)|T_i|\rfloor$ elements, and every element in $T_i$ was placed there by a current-array insertion (not by a successful cleanup attempt) of an insertion of epoch $i$;
--   3. if $t_{i+1}\le|xs|$, then after $t_{i+1}$ insertions every node of $T_i$ is full.
--
--   $$|T_i\text{ at time }t_i| = \lfloor(1-\eta)|T_i|\rfloor,\qquad T_i\text{ full at time }t_{i+1}.$$
--
--   The statement is deterministic: it holds for every outcome of the hash functions. It is the correctness half of the paper's insertion algorithm.
--
--   Differences from the source:
--   - reading: η is a small constant, fixed by (6) η ≤ 1/(400(λ+1)^6) for a sufficiently large λ → ∃ η₀ > 0 such that the claim holds for every η ∈ (0, η₀]; reason: (6) with λ ≥ λ₀ is exactly η ≤ 1/(400(λ₀+1)^6); the claim is for the construction's fixed η, which may be any sufficiently small value
--   - reading: §2 assumes n a power of two; App. A.1 handles arbitrary n assuming n ≥ 8 'without loss of generality' → every n ≥ 8, with the App. A.1 layout (which for n a power of two is the §2 layout); reason: the paper's construction is only defined for n ≥ 8; smaller tables are a constant-size case of Theorem 1.1 only
--   - encoding: time t_i (after t_i insertions), for an incremental sequence that reaches it → the clauses at times t_i and t_{i+1} are asserted when the key list has at least that many keys; reason: the table at time t depends only on the first t insertions
--   - encoding: elements with random hashes → keys of an arbitrary linearly ordered type K, an arbitrary outcome ω : Outcome K n; reason: the claim is deterministic, so it is stated for every outcome
--   - reading: 'place x in an empty slot of U', 'a nonfull child', the slot order inside nodes left to the implementation (§4: every touched node keeps its bit) → the fixed bit-preserving implementation of Def_IncrOpenAddr_NoTradeoff_Algorithm (first empty slot, first two slots sorted increasingly; left child when U is off the path; step 3 takes the first candidate slot of V); reason: the paper leaves these choices free; the statement is made for one admissible implementation
-- source:
--   Farach-Colton, Krapivin, Kuszmaul, Incremental Open Addressing Has No Time-Space Tradeoff, arXiv:2611.04186 (manuscript sha256 9486c2b8…), p. 10 (PDF 11), Lemma 2.2

import Mathlib
import Definitions.Def_IncrOpenAddr_NoTradeoff_Layout
import Definitions.Def_IncrOpenAddr_NoTradeoff_HashModel
import Definitions.Def_IncrOpenAddr_NoTradeoff_Algorithm
import Definitions.Def_IncrOpenAddr_NoTradeoff_Analysis

namespace IncrOpenAddr.NoTradeoff

theorem lemma_2_2 :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ n : ℕ, 8 ≤ n → ∀ (K : Type) [LinearOrder K] (ω : Outcome K n) (xs : List K),
        xs.Nodup → xs.length ≤ n →
        (∀ r ∈ recs .sec2 n η ω xs, r.s2.placed.isSome = true) ∧
        ∀ i : ℕ, 1 ≤ i → i < numTrees n →
          (epochEnd n η i ≤ xs.length →
            occupiedIn n (tableAt .sec2 n η ω xs (epochEnd n η i)) i =
                ⌊(1 - η) * (treeSize n i : ℝ)⌋₊ ∧
              ∀ v ∈ allNodes n, v.tree = i →
                ∀ z ∈ nodeElems n (tableAt .sec2 n η ω xs (epochEnd n η i)) v,
                  ∃ r ∈ (recs .sec2 n η ω xs).take (epochEnd n η i),
                    r.key = z ∧ r.epoch = i ∧ r.s2.cleanupOK = false ∧
                      r.s2.placed.map Node.tree = some i) ∧
          (epochEnd n η (i + 1) ≤ xs.length →
            ∀ v ∈ allNodes n, v.tree = i →
              nodeFull n (tableAt .sec2 n η ω xs (epochEnd n η (i + 1))) v = true) := by sorry

end IncrOpenAddr.NoTradeoff
