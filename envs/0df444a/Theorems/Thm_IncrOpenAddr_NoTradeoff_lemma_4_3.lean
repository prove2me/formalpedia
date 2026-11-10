-- Prove2me | Theorems.Thm_IncrOpenAddr_NoTradeoff_lemma_4_3
-- name    : IncrOpenAddr.NoTradeoff.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:37:59.560202+00:00
-- url     : https://prove2.me/theorems/73e7ac3c-9743-4cb6-9af0-d4629fb43c37
-- title:
--   Lemma 4.3 — after every insertion of epoch s every element is safe, even with I(x) replaced by min{I(x), s}
-- statement:
--   **Lemma 4.3.** For a sufficiently small constant $\eta>0$, every $n\ge8$, every outcome of the hashes and every list $xs$ of at most $n$ distinct keys inserted by the §4 algorithm: after every insertion $t\ge1$, made during epoch $s$, every key $z$ is safe in the table with $I(z)$ replaced by $\min\{I(z),s\}$, that is, every node holding $z$ lies in a tree $T_i$ with $i\le\min\{I(z),s,\alpha\}$ and is either an ancestor of $L_i(z)$ at level at most $J_i(z)$ (at most $\max\{J_1(z),\min\{I(z),s\}\}$ if $i=1$) or a node of $S_i(z)$.
--
--   $$z\in\text{node }v\ \Longrightarrow\ \text{the query for }z\text{ waits for }v\text{ (with }I(z)\leftarrow\min\{I(z),s\}).$$
--
--   Differences from the source:
--   - reading: η is a small constant, fixed by (6) η ≤ 1/(400(λ+1)^6) for a sufficiently large λ → ∃ η₀ > 0 such that the claim holds for every η ∈ (0, η₀]; reason: (6) with λ ≥ λ₀ is exactly η ≤ 1/(400(λ₀+1)^6); the claim is for the construction's fixed η, which may be any sufficiently small value
--   - reading: §2 assumes n a power of two; App. A.1 handles arbitrary n assuming n ≥ 8 'without loss of generality' → every n ≥ 8, with the App. A.1 layout (which for n a power of two is the §2 layout); reason: the paper's construction is only defined for n ≥ 8; smaller tables are a constant-size case of Theorem 1.1 only
--   - encoding: every element x in the table → every key z of K: the condition is about the nodes holding z, so it is empty for keys not in the table; reason: same statement
--   - encoding: elements with random hashes → an arbitrary outcome ω : Outcome K n; reason: the claim is deterministic
--   - reading: 'place x in an empty slot of U', 'a nonfull child', the slot order inside nodes left to the implementation (§4: every touched node keeps its bit) → the fixed bit-preserving implementation of Def_IncrOpenAddr_NoTradeoff_Algorithm (first empty slot, first two slots sorted increasingly; left child when U is off the path; step 3 takes the first candidate slot of V); reason: the paper leaves these choices free; the statement is made for one admissible implementation
-- source:
--   Farach-Colton, Krapivin, Kuszmaul, Incremental Open Addressing Has No Time-Space Tradeoff, arXiv:2611.04186 (manuscript sha256 9486c2b8…), p. 22 (PDF 23), Lemma 4.3

import Mathlib
import Definitions.Def_IncrOpenAddr_NoTradeoff_Layout
import Definitions.Def_IncrOpenAddr_NoTradeoff_HashModel
import Definitions.Def_IncrOpenAddr_NoTradeoff_Algorithm
import Definitions.Def_IncrOpenAddr_NoTradeoff_Analysis

namespace IncrOpenAddr.NoTradeoff

theorem lemma_4_3 :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ n : ℕ, 8 ≤ n → ∀ (K : Type) [LinearOrder K] (ω : Outcome K n) (xs : List K),
        xs.Nodup → xs.length ≤ n →
        ∀ t : ℕ, 1 ≤ t → t ≤ xs.length → ∀ z : K,
          Safe n (tableAt .sec4 n η ω xs t) ω z
            (min (Iof n (tableAt .sec4 n η ω xs t) ω z) (epochOf n η (t - 1) : ℕ∞)) := by sorry

end IncrOpenAddr.NoTradeoff
