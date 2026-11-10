-- Prove2me | Theorems.Thm_IncrOpenAddr_NoTradeoff_lemma_2_8
-- name    : IncrOpenAddr.NoTradeoff.lemma_2_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:38:18.298038+00:00
-- url     : https://prove2.me/theorems/fc408d67-e30b-4f66-a5e1-d5c5e518e5c9
-- title:
--   Lemma 2.8 — a level-j subtree is bad with probability at most e^{−2^{j/5}}
-- statement:
--   **Lemma 2.8 (Probability of a bad subtree).** There is $\lambda_0$ such that for every $\lambda\ge\lambda_0$ and every $\eta$ with $0<\eta\le1/(400(\lambda+1)^6)$ (condition (6)), for every $n\ge8$, every list $xs$ of at most $n$ distinct keys inserted by the §2 algorithm, every tree $T_i$ with $i+1\le\alpha$, every level $\lambda<j\le h_i$ and every node $T_i[j,k]$ (when $xs$ reaches the end of phase $j$ of epoch $i+1$),
--   $$\mathbb P\big(Z_{i,j,k}=1\big)\ \le\ e^{-2^{j/5}},\tag{9}$$
--   the probability taken over the hashes (uniform leaves, uniform priorities, all independent). The bound is doubly exponential in the level.
--
--   Differences from the source:
--   - reading: λ a sufficiently large constant and η satisfying (6) → ∃ λ₀ ∀ λ ≥ λ₀ ∀ η with 0 < η ≤ 1/(400(λ+1)^6); reason: the standing assumption of §2.4, quantified before n and the keys
--   - reading: §2 assumes n a power of two; App. A.1 handles arbitrary n assuming n ≥ 8 'without loss of generality' → every n ≥ 8, with the App. A.1 layout (which for n a power of two is the §2 layout); reason: the paper's construction is only defined for n ≥ 8; smaller tables are a constant-size case of Theorem 1.1 only
--   - encoding: elements with fully random hashes L_i(x), g_i(x) → keys from an arbitrary finite linearly ordered type K; the law hashLaw K n makes all L_i(x) uniform on the leaves of T_i and all g_i(x) uniform on [0,1], all independent; the inserted keys are a duplicate-free list xs of length ≤ n; reason: only the hashes of the finitely many keys involved matter, so a finite key universe changes no instance; the order on K is the order used by the §4 node bits
--   - reading: P(Z_{i,j,k} = 1) for the run of the algorithm → for every key list that reaches the end of phase j of epoch i+1 (phaseEnd n η (i+1) j ≤ |xs|); reason: Z counts the direct attempts of phases up to j of epoch i+1, which exist only if the run reaches them
--   - reading: 'place x in an empty slot of U', 'a nonfull child', the slot order inside nodes left to the implementation (§4: every touched node keeps its bit) → the fixed bit-preserving implementation of Def_IncrOpenAddr_NoTradeoff_Algorithm (first empty slot, first two slots sorted increasingly; left child when U is off the path; step 3 takes the first candidate slot of V); reason: the paper leaves these choices free; the statement is made for one admissible implementation
-- source:
--   Farach-Colton, Krapivin, Kuszmaul, Incremental Open Addressing Has No Time-Space Tradeoff, arXiv:2611.04186 (manuscript sha256 9486c2b8…), p. 14 (PDF 15), Lemma 2.8, Eq. (9)

import Mathlib
import Definitions.Def_IncrOpenAddr_NoTradeoff_Layout
import Definitions.Def_IncrOpenAddr_NoTradeoff_HashModel
import Definitions.Def_IncrOpenAddr_NoTradeoff_Algorithm
import Definitions.Def_IncrOpenAddr_NoTradeoff_Analysis
open MeasureTheory

namespace IncrOpenAddr.NoTradeoff

theorem lemma_2_8 :
    ∃ lam0 : ℕ, ∀ lam : ℕ, lam0 ≤ lam → ∀ η : ℝ, 0 < η → η ≤ 1 / (400 * ((lam : ℝ) + 1) ^ 6) →
      ∀ n : ℕ, 8 ≤ n → ∀ (K : Type) [Fintype K] [LinearOrder K] (xs : List K),
        xs.Nodup → xs.length ≤ n →
        ∀ i j k : ℕ, 1 ≤ i → i + 1 ≤ numTrees n → lam < j → j ≤ height n i →
          k < 2 ^ (height n i - j) → phaseEnd n η (i + 1) j ≤ xs.length →
          hashLaw K n {ω | Zb lam n η ω xs i j k = true} ≤
            ENNReal.ofReal (Real.exp (-(2 : ℝ) ^ ((j : ℝ) / 5))) := by sorry

end IncrOpenAddr.NoTradeoff
