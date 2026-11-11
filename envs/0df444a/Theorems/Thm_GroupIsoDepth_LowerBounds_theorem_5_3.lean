-- Prove2me | Theorems.Thm_GroupIsoDepth_LowerBounds_theorem_5_3
-- name    : GroupIsoDepth.LowerBounds.theorem_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:41:29.305207+00:00
-- url     : https://prove2.me/theorems/bedb91b9-4e6c-4747-8ec7-a097a5443e93
-- title:
--   Theorem 5.3 — CNFs for promise GpI on groups of order $n=2^{2k}$ need $n^{\Omega(\log n)}$ clauses, exponent constant $\ge 1/16$, already on abelian groups of exponent 4
-- statement:
--   Any (uniform or non-uniform) CNF solving the promise Group Isomorphism problem on multiplication tables of groups of order $n=2^{2k}$ has size at least $n^{\Omega(\log n)}$; the groups used are abelian of exponent 4, and the constant in the exponent is at least $1/16$. Precisely: there is a constant $C$ such that for every $k\ge1$, with $n=4^k$,
--   1. every CNF over the $2n^2\lceil\log_2 n\rceil$ input bits of a pair of tables of order $n$ that, on every pair of valid group tables, outputs 1 iff the two groups are isomorphic, has at least $n^{\frac1{16}\log_2 n-C}$ clauses;
--   2. the same holds for every CNF that is only required to be correct on pairs of tables of abelian groups of exponent dividing 4.
--
--   Differences from the source:
--   - reading: size at least n^{Ω(log n)} ... the constant in the exponent is at least 1/16 → ∃ C, ∀ k ≥ 1: every such CNF has ≥ (4^k)^{(1/16)·log₂ 4^k − C} clauses; reason: the exponent is (1/16)·log₂ n minus a constant, as the proof's displayed m ≥ n^{(1/16)(log₂ n)−1} (p. 40); the proof gives m ≥ 2^{ks−s²−2k} at the integer s = ⌊k/2⌋, i.e. n^{(1/16)log₂ n − 1} for even k and 2^{−1/4} times that for odd k, so C is left existential (C = 9/8 suffices); k ≥ 1 because at k = 0 (n = 1, no input bits) the empty CNF is correct
--   - generalization: the bound for CNFs correct on all pairs of valid group tables; 'The groups we use for the lower bound will be Abelian of exponent 4' → clause 2: the same bound for CNFs required to be correct only on pairs of abelian tables with x⁴ = e; reason: the sentence after the theorem, as a statement; clause 2 implies clause 1 (an abelian exponent-4 table is a valid group table), and clause 1 is stated too
--   - encoding: the promise Group Isomorphism problem → (∀ x, both tables valid → (CNF.Holds φ x ↔ TableIso …)); arbitrary output elsewhere; reason: the promise version of §5 intro
--   - reading: size of a CNF → number of clauses (Finset card); reason: the proof bounds the number m of clauses of C = Γ₁ ∧ ⋯ ∧ Γ_m
--   - encoding: a CNF/DNF as a conjunction/disjunction of clauses/terms, each of literals → Finset of clauses/terms, each a Finset of literals (v, b) (published LiftSAParity.Clause/CNF); size = card; reason: identical clauses or terms are counted once, which can only lower the size; so the lower bound is at least as strong
--   - encoding: order n = 2^{2k} → n = 4 ^ k; reason: same numbers
--   - encoding: T ≅ T': a bijection σ of [n] with σ(T(a,b)) = T'(σa, σb) → TableIso: ∃ σ : Equiv.Perm (Fin n), ∀ a b c, T a b = c ↔ T' (σ a) (σ b) = σ c; reason: avoids range proofs; on valid tables (entries in [n], as GpI requires) it is exactly σ(T(a,b)) = T'(σa, σb)
--   - encoding: log n, n^{log n} → Real.logb 2 n and real powers (Real.rpow); reason: the paper's log is log₂ (§1, p. 1; proof of Thm 5.3, p. 40)
--   - encoding: each entry a ⌈log₂ n⌉-bit label of an element of [n] (bit order not fixed) → TableVar n = Fin n × Fin n × Fin (Nat.clog 2 n); entry = Σ_b x(i,j,b)·2^b (bit b has weight 2^b); labels [n] = Fin n = {0,…,n−1}; reason: any fixed bit order and label set is a renaming of the input variables; no instance and no size changes
-- source:
--   Grochow, Kardeş, Levet, Group Isomorphism: Depth-2½ Circuits and Lower Bounds, STOC 2027 submission (manuscript sha256 cd6cacd4…), Theorem 5.3 (stated p. 36, PDF 37; proved p. 40, PDF 41)

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_GroupIsoDepth_LowerBounds_Circuits
import Definitions.Def_GroupIsoDepth_LowerBounds_CayleyTables

open LiftSAParity

namespace GroupIsoDepth.LowerBounds

/-- Theorem 5.3 (stated printed p. 36 / PDF 37, proved p. 40 / PDF 41). Any CNF solving the promise
Group Isomorphism problem on multiplication tables of groups of order `n = 2^{2k}` has size at least
`n^{Ω(log n)}`; the hard groups are abelian of exponent 4, and the constant in the exponent is at
least `1/16`: there is a constant `C` such that for every `k ≥ 1`, with `n = 4^k`, every CNF over the
`2n²⌈log₂ n⌉` input bits that is correct on all pairs of valid group tables of order `n` — and even
every CNF that is only correct on all pairs of tables of abelian groups of exponent dividing 4 — has
at least `n^{(1/16) log₂ n − C}` clauses. -/
theorem theorem_5_3 :
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k →
      (∀ φ : CNF (PairVar (4 ^ k)),
        (∀ x, IsGroupTable (entry (fst x)) → IsGroupTable (entry (snd x)) →
          (CNF.Holds φ x ↔ TableIso (entry (fst x)) (entry (snd x)))) →
        ((4 ^ k : ℕ) : ℝ) ^ (1 / 16 * Real.logb 2 ((4 ^ k : ℕ) : ℝ) - C) ≤ (φ.card : ℝ)) ∧
      (∀ φ : CNF (PairVar (4 ^ k)),
        (∀ x, IsAbelianExp4Table (entry (fst x)) → IsAbelianExp4Table (entry (snd x)) →
          (CNF.Holds φ x ↔ TableIso (entry (fst x)) (entry (snd x)))) →
        ((4 ^ k : ℕ) : ℝ) ^ (1 / 16 * Real.logb 2 ((4 ^ k : ℕ) : ℝ) - C) ≤ (φ.card : ℝ)) := by sorry

end GroupIsoDepth.LowerBounds
