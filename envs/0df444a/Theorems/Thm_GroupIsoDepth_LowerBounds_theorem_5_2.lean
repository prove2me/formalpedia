-- Prove2me | Theorems.Thm_GroupIsoDepth_LowerBounds_theorem_5_2
-- name    : GroupIsoDepth.LowerBounds.theorem_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:41:32.276506+00:00
-- url     : https://prove2.me/theorems/37c834fa-544b-4b2b-9887-49ec79679f28
-- title:
--   Theorem 5.2 — DNFs for group-table validity and for GpI need $n!/n^{\log n}\ge2^{n\log n-O(n)}$ terms; for Latin squares $(n!)^{2n}/n^{n^2}\ge2^{n^2\log n-O(n^2)}$
-- statement:
--   Let $N=n^2\lceil\log_2 n\rceil$ be the number of input bits of a multiplication table of order $n$. There is a constant $C$ such that for every $n\ge1$:
--   1. every (uniform or non-uniform) DNF on the $N$ bits that is 1 on all Cayley tables of groups and 0 on all other multiplication tables has at least $n!/n^{\log_2 n}$ terms, and $n!/n^{\log_2 n}\ge 2^{n\log_2 n-Cn}$;
--   2. hence every DNF on the $2N$ bits of a pair of tables that decides (total) Group Isomorphism has at least $n!/n^{\log_2 n}$ terms (so also at least $2^{n\log_2 n-Cn}$);
--   3. every DNF on the $N$ bits that is 1 exactly on the Latin squares has at least $(n!)^{2n}/n^{n^2}$ terms, and $(n!)^{2n}/n^{n^2}\ge 2^{n^2\log_2 n-Cn^2}$.
--
--   Differences from the source:
--   - reading: DNF on multiplication tables of order n that is 1 on all Cayley tables of groups and 0 on all other multiplication tables → DNF over all N = n²⌈log₂ n⌉ input bits with DNF(x) ↔ x ∈ VALID_n for every bit string x (out-of-range labels included); reason: Lemma 4.2's VALID_n checks the range of every entry; the width argument of the proof needs every bit string to be an input
--   - encoding: tables of order n → 1 ≤ n; reason: there is no group or quasigroup of order 0
--   - encoding: O(n) and O(n²) in the exponents → one constant C, chosen before n, with the inequalities for every n ≥ 1; reason: the asymptotic notation made explicit; one constant for both terms is equivalent to two (take the maximum)
--   - reading: Hence the same lower bound holds on DNFs for GpI → every DNF over the 2N bits of a pair deciding total GpI has ≥ n!/n^{log₂ n} terms; the 2^{n log n − O(n)} form follows from clause 1's inequality; reason: the same bound, stated once
--   - reading: a circuit deciding Group Isomorphism on tables of order n → correct on every one of the 2^{2N} bit strings, including invalid tables and out-of-range labels (the total language: both tables valid group tables and isomorphic); reason: §4.1 (p. 24): the paper solves 'the total GpI problem rather than the promise problem', and Lemma 4.2 checks that entries lie in [n]
--   - encoding: a CNF/DNF as a conjunction/disjunction of clauses/terms, each of literals → Finset of clauses/terms, each a Finset of literals (v, b) (published LiftSAParity.Clause/CNF); size = card; reason: identical clauses or terms are counted once, which can only lower the size; so the lower bound is at least as strong
--   - encoding: log n, n^{log n} → Real.logb 2 n and real powers (Real.rpow); reason: the paper's log is log₂ (§1, p. 1; proof of Thm 5.3, p. 40)
--   - encoding: each entry a ⌈log₂ n⌉-bit label of an element of [n] (bit order not fixed) → TableVar n = Fin n × Fin n × Fin (Nat.clog 2 n); entry = Σ_b x(i,j,b)·2^b (bit b has weight 2^b); labels [n] = Fin n = {0,…,n−1}; reason: any fixed bit order and label set is a renaming of the input variables; no instance and no size changes
-- source:
--   Grochow, Kardeş, Levet, Group Isomorphism: Depth-2½ Circuits and Lower Bounds, STOC 2027 submission (manuscript sha256 cd6cacd4…), Theorem 5.2 (p. 36, PDF 37)

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_GroupIsoDepth_LowerBounds_Circuits
import Definitions.Def_GroupIsoDepth_LowerBounds_CayleyTables

namespace GroupIsoDepth.LowerBounds

/-- Theorem 5.2 (printed p. 36, PDF 37). There is a constant `C` (the `O(n)` and `O(n²)` terms) such
that for every order `n ≥ 1`:
1. every DNF over the `N = n²⌈log₂ n⌉` input bits of one table that is 1 exactly on the Cayley tables
   of groups has at least `n!/n^{log₂ n}` terms, and `n!/n^{log₂ n} ≥ 2^{n log₂ n − C n}`;
2. every DNF over the `2N` input bits of a pair of tables deciding (total) Group Isomorphism has at
   least `n!/n^{log₂ n}` terms;
3. every DNF over the `N` input bits of one table that is 1 exactly on the Latin squares has at least
   `(n!)^{2n}/n^{n²}` terms, and `(n!)^{2n}/n^{n²} ≥ 2^{n² log₂ n − C n²}`. -/
theorem theorem_5_2 :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      ((∀ ψ : DNF (TableVar n), (∀ x, DNF.Holds ψ x ↔ ValidGroup n x) →
          (n.factorial : ℝ) / (n : ℝ) ^ Real.logb 2 n ≤ (ψ.card : ℝ)) ∧
        (2 : ℝ) ^ ((n : ℝ) * Real.logb 2 n - C * n) ≤
          (n.factorial : ℝ) / (n : ℝ) ^ Real.logb 2 n) ∧
      (∀ ψ : DNF (PairVar n), (∀ x, DNF.Holds ψ x ↔ GpI n x) →
          (n.factorial : ℝ) / (n : ℝ) ^ Real.logb 2 n ≤ (ψ.card : ℝ)) ∧
      ((∀ ψ : DNF (TableVar n), (∀ x, DNF.Holds ψ x ↔ LatinSq n x) →
          (n.factorial : ℝ) ^ (2 * n) / (n : ℝ) ^ (n ^ 2) ≤ (ψ.card : ℝ)) ∧
        (2 : ℝ) ^ ((n : ℝ) ^ 2 * Real.logb 2 n - C * (n : ℝ) ^ 2) ≤
          (n.factorial : ℝ) ^ (2 * n) / (n : ℝ) ^ (n ^ 2)) := by sorry

end GroupIsoDepth.LowerBounds
