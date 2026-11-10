-- Prove2me | Theorems.Thm_IncrOpenAddr_NoTradeoff_lemma_2_7
-- name    : IncrOpenAddr.NoTradeoff.lemma_2_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:38:05.163966+00:00
-- url     : https://prove2.me/theorems/ec7c0c4b-56b0-4b6f-851e-d6a00800c77e
-- title:
--   Lemma 2.7 — a level-j subtree (j > λ) that is not bad is full by the end of phase j of epoch i + 1
-- statement:
--   **Lemma 2.7.** There is $\lambda_0$ such that for every $\lambda\ge\lambda_0$, every $\eta$ with $0<\eta\le 1/(400(\lambda+1)^6)$ (condition (6)), every $n\ge8$, every outcome of the hashes and every list $xs$ of at most $n$ distinct keys inserted by the §2 algorithm: for every tree $T_i$ with $i+1\le\alpha$, every level $j$ with $\lambda<j\le h_i$ and every node $T_i[j,k]$,
--   $$Z_{i,j,k}=0\ \Longrightarrow\ \text{the subtree of }T_i[j,k]\text{ is full by the end of phase }j\text{ of epoch }i+1,$$
--   provided the list reaches the end of that phase. $Z$ is the bad-subtree indicator (8) built from the direct-attempt counts of the same run.
--
--   Together with Lemma 2.8 this says that the cleanup phases fill almost every subtree on schedule; it is deterministic.
--
--   Differences from the source:
--   - reading: λ a sufficiently large constant and η satisfying (6) → ∃ λ₀ ∀ λ ≥ λ₀ ∀ η with 0 < η ≤ 1/(400(λ+1)^6); reason: the standing assumption of §2.4, quantified before n and the keys
--   - reading: §2 assumes n a power of two; App. A.1 handles arbitrary n assuming n ≥ 8 'without loss of generality' → every n ≥ 8, with the App. A.1 layout (which for n a power of two is the §2 layout); reason: the paper's construction is only defined for n ≥ 8; smaller tables are a constant-size case of Theorem 1.1 only
--   - encoding: 'by the end of phase j of epoch i + 1' → the table after phaseEnd n η (i+1) j insertions, asserted when xs has at least that many keys; reason: the table at a time depends only on the insertions up to it
--   - encoding: elements with random hashes → an arbitrary outcome ω : Outcome K n; reason: the claim is deterministic
--   - reading: 'place x in an empty slot of U', 'a nonfull child', the slot order inside nodes left to the implementation (§4: every touched node keeps its bit) → the fixed bit-preserving implementation of Def_IncrOpenAddr_NoTradeoff_Algorithm (first empty slot, first two slots sorted increasingly; left child when U is off the path; step 3 takes the first candidate slot of V); reason: the paper leaves these choices free; the statement is made for one admissible implementation
-- source:
--   Farach-Colton, Krapivin, Kuszmaul, Incremental Open Addressing Has No Time-Space Tradeoff, arXiv:2611.04186 (manuscript sha256 9486c2b8…), p. 13 (PDF 14), Lemma 2.7

import Mathlib
import Definitions.Def_IncrOpenAddr_NoTradeoff_Layout
import Definitions.Def_IncrOpenAddr_NoTradeoff_HashModel
import Definitions.Def_IncrOpenAddr_NoTradeoff_Algorithm
import Definitions.Def_IncrOpenAddr_NoTradeoff_Analysis

namespace IncrOpenAddr.NoTradeoff

theorem lemma_2_7 :
    ∃ lam0 : ℕ, ∀ lam : ℕ, lam0 ≤ lam → ∀ η : ℝ, 0 < η → η ≤ 1 / (400 * ((lam : ℝ) + 1) ^ 6) →
      ∀ n : ℕ, 8 ≤ n → ∀ (K : Type) [LinearOrder K] (ω : Outcome K n) (xs : List K),
        xs.Nodup → xs.length ≤ n →
        ∀ i j k : ℕ, 1 ≤ i → i + 1 ≤ numTrees n → lam < j → j ≤ height n i →
          k < 2 ^ (height n i - j) →
          Zb lam n η ω xs i j k = false → phaseEnd n η (i + 1) j ≤ xs.length →
          subtreeFull n (tableAt .sec2 n η ω xs (phaseEnd n η (i + 1) j)) ⟨i, j, k⟩ = true := by sorry

end IncrOpenAddr.NoTradeoff
