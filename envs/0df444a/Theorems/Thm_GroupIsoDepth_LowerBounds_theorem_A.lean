-- Prove2me | Theorems.Thm_GroupIsoDepth_LowerBounds_theorem_A
-- name    : GroupIsoDepth.LowerBounds.theorem_A
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:41:33.556341+00:00
-- url     : https://prove2.me/theorems/8209e54d-b0f3-46ab-a7fa-e1f032989ddb
-- title:
--   Theorem A — every depth-2 circuit (CNF or DNF) deciding Group Isomorphism of Cayley tables has size $|G|^{\Omega(\log|G|)}$
-- statement:
--   Any (uniform or non-uniform) family of depth-2 circuits deciding Group Isomorphism requires size $|G|^{\Omega(\log|G|)}$. Precisely: there are a constant $c>0$ and $K\in\mathbb N$ such that for every $k\ge K$, with $n=4^k=2^{2k}$, every depth-2 circuit — a CNF or a DNF — over the $2n^2\lceil\log_2 n\rceil$ input bits encoding a pair of $n\times n$ tables (each entry a $\lceil\log_2 n\rceil$-bit label) that decides the total Group Isomorphism language (outputs 1 exactly on the pairs of valid group tables that are isomorphic, and is correct on every bit string) has size (number of clauses, resp. terms) at least $n^{c\log_2 n}$.
--
--   Differences from the source:
--   - reading: a family of depth-2 circuits ... requires size |G|^{Ω(log |G|)} → ∃ c > 0, ∃ K, ∀ k ≥ K, at n = 4^k: every depth-2 circuit deciding GpI on order-n inputs has size ≥ n^{c·log₂ n}; reason: the paper proves the CNF half (Theorem 5.3) only at orders n = 2^{2k}; this per-length form implies that every family has size ≥ n^{c log n} at infinitely many n; c and K come before k and the circuit
--   - reading: size of a depth-2 circuit → number of clauses (CNF) resp. terms (DNF); reason: the paper's own measure in Theorems 5.2 and 5.3; a gate count differs by at most 1 + the number of width-1 clauses (≤ 2·#variables, polynomial in n), which n^{Ω(log n)} absorbs
--   - encoding: uniform or non-uniform → no uniformity condition: every circuit at every length is quantified; reason: the bound holds circuit by circuit
--   - reading: a circuit deciding Group Isomorphism on tables of order n → correct on every one of the 2^{2N} bit strings, including invalid tables and out-of-range labels (the total language: both tables valid group tables and isomorphic); reason: §4.1 (p. 24): the paper solves 'the total GpI problem rather than the promise problem', and Lemma 4.2 checks that entries lie in [n]
--   - encoding: a CNF/DNF as a conjunction/disjunction of clauses/terms, each of literals → Finset of clauses/terms, each a Finset of literals (v, b) (published LiftSAParity.Clause/CNF); size = card; reason: identical clauses or terms are counted once, which can only lower the size; so the lower bound is at least as strong
--   - encoding: order n = 2^{2k} → n = 4 ^ k; reason: same numbers
--   - encoding: T ≅ T': a bijection σ of [n] with σ(T(a,b)) = T'(σa, σb) → TableIso: ∃ σ : Equiv.Perm (Fin n), ∀ a b c, T a b = c ↔ T' (σ a) (σ b) = σ c; reason: avoids range proofs; on valid tables (entries in [n], as GpI requires) it is exactly σ(T(a,b)) = T'(σa, σb)
--   - encoding: log n, n^{log n} → Real.logb 2 n and real powers (Real.rpow); reason: the paper's log is log₂ (§1, p. 1; proof of Thm 5.3, p. 40)
--   - encoding: each entry a ⌈log₂ n⌉-bit label of an element of [n] (bit order not fixed) → TableVar n = Fin n × Fin n × Fin (Nat.clog 2 n); entry = Σ_b x(i,j,b)·2^b (bit b has weight 2^b); labels [n] = Fin n = {0,…,n−1}; reason: any fixed bit order and label set is a renaming of the input variables; no instance and no size changes
-- source:
--   Grochow, Kardeş, Levet, Group Isomorphism: Depth-2½ Circuits and Lower Bounds, STOC 2027 submission (manuscript sha256 cd6cacd4…), Theorem A (p. 2, PDF 3); restated in §2 (p. 12, PDF 13) and §5 intro (p. 35, PDF 36); follows from Theorem 5.2 (p. 36, PDF 37) and Theorem 5.3 (p. 36 / PDF 37, proved p. 40 / PDF 41)

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_GroupIsoDepth_LowerBounds_Circuits
import Definitions.Def_GroupIsoDepth_LowerBounds_CayleyTables

namespace GroupIsoDepth.LowerBounds

/-- Theorem A (printed p. 2, PDF 3). Any (uniform or non-uniform) family of depth-2 circuits deciding
Group Isomorphism requires size `|G|^{Ω(log |G|)}`: there are `c > 0` and `K` such that for every
`k ≥ K`, with `n = 4^k = 2^{2k}`, every depth-2 circuit (a CNF or a DNF) over the `2n²⌈log₂ n⌉` input
bits of a pair of tables of order `n` that decides the total Group Isomorphism language (correct on
every bit string) has size (number of clauses, resp. terms) at least `n^{c log₂ n}`. -/
theorem theorem_A :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ φ : Depth2 (PairVar (4 ^ k)), Depth2.Decides φ (GpI (4 ^ k)) →
        ((4 ^ k : ℕ) : ℝ) ^ (c * Real.logb 2 ((4 ^ k : ℕ) : ℝ)) ≤ (Depth2.size φ : ℝ) := by sorry

end GroupIsoDepth.LowerBounds
