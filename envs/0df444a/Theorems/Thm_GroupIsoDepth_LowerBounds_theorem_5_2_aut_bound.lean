-- Prove2me | Theorems.Thm_GroupIsoDepth_LowerBounds_theorem_5_2_aut_bound
-- name    : GroupIsoDepth.LowerBounds.theorem_5_2_aut_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:41:18.670196+00:00
-- url     : https://prove2.me/theorems/f605aec5-88bd-4abc-ada0-1dd78cca6dfe
-- title:
--   Theorem 5.2, proof (automorphism bound) — $|\mathrm{Aut}(G)|\le n^{\log n}$, hence at least $n!/n^{\log n}$ labelled tables per group
-- statement:
--   1. Every finite group $G$ of order $n$ has at most $n^{\log_2 n}$ automorphisms.
--   2. Consequently, for every group $G$ of order $n$ there are at least $n!/n^{\log_2 n}$ distinct multiplication tables of order $n$ (bit strings of length $n^2\lceil\log_2 n\rceil$) that are Cayley tables of $G$, i.e. that equal $T(a,b)=e^{-1}(e(a)e(b))$ for some bijection $e:[n]\to G$.
--
--   Differences from the source:
--   - reading: there are at least n!/n^{log n} distinct tables corresponding to each group → the number of bit-tables x of order n that represent G (∃ bijection e : [n] → G with entry x a b = e⁻¹(e a · e b)) is ≥ n!/n^{log₂ n}; reason: 'tables corresponding to G' are the labelled Cayley tables of G on [n]
--   - encoding: automorphism group of G → Nat.card (G ≃* G); reason: Mathlib's multiplicative automorphisms
--   - encoding: log n, n^{log n} → Real.logb 2 n and real powers (Real.rpow); reason: the paper's log is log₂ (§1, p. 1; proof of Thm 5.3, p. 40)
--   - encoding: each entry a ⌈log₂ n⌉-bit label of an element of [n] (bit order not fixed) → TableVar n = Fin n × Fin n × Fin (Nat.clog 2 n); entry = Σ_b x(i,j,b)·2^b (bit b has weight 2^b); labels [n] = Fin n = {0,…,n−1}; reason: any fixed bit order and label set is a renaming of the input variables; no instance and no size changes
-- source:
--   Grochow, Kardeş, Levet, Group Isomorphism: Depth-2½ Circuits and Lower Bounds, STOC 2027 submission (manuscript sha256 cd6cacd4…), proof of Theorem 5.2 (p. 36, PDF 37)

import Mathlib
import Definitions.Def_GroupIsoDepth_LowerBounds_CayleyTables

namespace GroupIsoDepth.LowerBounds

universe u

/-- Proof of Theorem 5.2, automorphism bound (printed p. 36, PDF 37): a group of order `n` has at
most `n^{log₂ n}` automorphisms, so for each group `G` of order `n` there are at least
`n!/n^{log₂ n}` distinct labelled tables on `[n]` that are Cayley tables of `G`. -/
theorem theorem_5_2_aut_bound :
    (∀ (G : Type u) [Group G] [Fintype G],
      (Nat.card (G ≃* G) : ℝ) ≤ (Fintype.card G : ℝ) ^ Real.logb 2 (Fintype.card G)) ∧
    (∀ (n : ℕ) (G : Type u) [Group G] [Fintype G], Fintype.card G = n →
      (n.factorial : ℝ) / (n : ℝ) ^ Real.logb 2 n ≤
        (Nat.card {x : TableVar n → Bool // RepresentsGroup x G} : ℝ)) := by sorry

end GroupIsoDepth.LowerBounds
