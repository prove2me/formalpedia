-- Prove2me | Theorems.Thm_IncrOpenAddr_NoTradeoff_eq_15
-- name    : IncrOpenAddr.NoTradeoff.eq_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:38:17.060206+00:00
-- url     : https://prove2.me/theorems/dfa92ff4-522c-4f7b-810c-fcf49c387d25
-- title:
--   §4.2, Eq. (15) — for a key not in the table, P(I(x) ≥ 100b) = O(b^{−3}) for every b ≥ 2, hence E[I(x)²] = O(1)
-- statement:
--   **Eq. (15).** For a sufficiently small constant $\eta>0$ there is a constant $C$ such that for every $n\ge8$, every list $xs$ of at most $n$ distinct keys inserted by the §4 algorithm, every time $t\le|xs|$ and every key $x$ that is not among the first $t$ inserted keys, with $I(x)$ computed in the table after $t$ insertions,
--   $$\mathbb P\big(I(x)\ge100\,b\big)\ \le\ C\,b^{-3}\quad\text{for every real }b\ge2,\qquad\text{and}\qquad \mathbb E\big[I(x)^2\big]\le C.\tag{15}$$
--
--   This is the bound on how many trees a negative query must search; it is the last ingredient of the $O(1)$ expected negative-query time.
--
--   Differences from the source:
--   - reading: η is a small constant, fixed by (6) η ≤ 1/(400(λ+1)^6) for a sufficiently large λ → ∃ η₀ > 0 such that the claim holds for every η ∈ (0, η₀]; reason: (6) with λ ≥ λ₀ is exactly η ≤ 1/(400(λ₀+1)^6); the claim is for the construction's fixed η, which may be any sufficiently small value
--   - reading: §2 assumes n a power of two; App. A.1 handles arbitrary n assuming n ≥ 8 'without loss of generality' → every n ≥ 8, with the App. A.1 layout (which for n a power of two is the §2 layout); reason: the paper's construction is only defined for n ≥ 8; smaller tables are a constant-size case of Theorem 1.1 only
--   - encoding: elements with fully random hashes L_i(x), g_i(x) → keys from an arbitrary finite linearly ordered type K; the law hashLaw K n makes all L_i(x) uniform on the leaves of T_i and all g_i(x) uniform on [0,1], all independent; the inserted keys are a duplicate-free list xs of length ≤ n; reason: only the hashes of the finitely many keys involved matter, so a finite key universe changes no instance; the order on K is the order used by the §4 node bits
--   - reading: 'fix some element x and a time when x is not present' → x not among the first t keys of xs, I(x) in the table after t insertions; reason: the table at time t depends only on the first t insertions
--   - reading: O(b^{−3}) and O(1) → one ∃ C (after η, before n, the keys, t, x and b) for both bounds; reason: explicit constants
--   - reading: 'place x in an empty slot of U', 'a nonfull child', the slot order inside nodes left to the implementation (§4: every touched node keeps its bit) → the fixed bit-preserving implementation of Def_IncrOpenAddr_NoTradeoff_Algorithm (first empty slot, first two slots sorted increasingly; left child when U is off the path; step 3 takes the first candidate slot of V); reason: the paper leaves these choices free; the statement is made for one admissible implementation
-- source:
--   Farach-Colton, Krapivin, Kuszmaul, Incremental Open Addressing Has No Time-Space Tradeoff, arXiv:2611.04186 (manuscript sha256 9486c2b8…), p. 24–25 (PDF 25–26), §4.2, Eq. (15)

import Mathlib
import Definitions.Def_IncrOpenAddr_NoTradeoff_Layout
import Definitions.Def_IncrOpenAddr_NoTradeoff_HashModel
import Definitions.Def_IncrOpenAddr_NoTradeoff_Algorithm
import Definitions.Def_IncrOpenAddr_NoTradeoff_Analysis
open MeasureTheory
open scoped ENNReal

namespace IncrOpenAddr.NoTradeoff

theorem eq_15 :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∃ C : ℝ, ∀ n : ℕ, 8 ≤ n → ∀ (K : Type) [Fintype K] [LinearOrder K] (xs : List K),
        xs.Nodup → xs.length ≤ n →
        ∀ (t : ℕ) (x : K), t ≤ xs.length → x ∉ xs.take t →
          (∀ b : ℝ, 2 ≤ b →
            hashLaw K n {ω | ENNReal.ofReal (100 * b) ≤
                ((Iof n (tableAt .sec4 n η ω xs t) ω x : ℕ∞) : ℝ≥0∞)} ≤
              ENNReal.ofReal (C * b ^ (-3 : ℤ))) ∧
          ∫⁻ ω, ((Iof n (tableAt .sec4 n η ω xs t) ω x : ℕ∞) : ℝ≥0∞) ^ 2 ∂(hashLaw K n) ≤
            ENNReal.ofReal C := by sorry

end IncrOpenAddr.NoTradeoff
