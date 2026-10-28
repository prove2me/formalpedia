-- Prove2me | Theorems.Thm_MonoReset_IntervalBFS_lemma_1
-- name    : MonoReset.IntervalBFS.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:25.168981+00:00
-- url     : https://prove2.me/theorems/12dd1eae-e79a-4d83-b438-a97af1163e27
-- title:
--   Lemma 1, p. 2 (corrected: or empty) — under a monotonic automaton the preimage δ⁻¹(τ, I) of an interval is empty or an interval
-- statement:
--   Let $(S, \Sigma, \delta)$ be a monotonic automaton on the cyclically ordered states $s_1, \dots, s_n$. For every word $\tau \in \Sigma^*$ and every interval $I$, the preimage
--   $$\delta^{-1}(\tau, I) = \{s \in S : \delta(\tau, s) \in I\}$$
--   is either empty or an interval, i.e. equal to $[s_i, s_j]$ for some states $s_i, s_j$.
--
--   The lemma is what makes the preimage table of the algorithm well defined, and it is used in Lemmas 4 and 5.
--
--   **Formalization Note** States are `Fin n`, with $s_i$ the element $i-1$ and the cyclic order $0 \to 1 \to \cdots \to n-1 \to 0$; letters are `Fin k`; a word is a list read left to right. An interval $[s_i, s_j]$ is its pair of endpoints, and ∞ is `none`. Monotonicity is read cyclically (see the definition item).
--
--   Differences from the source:
--   - correction: δ−1(τ, I) is an interval → δ−1(τ, I) is empty or equal to ivSet J for some J; reason: intervals are nonempty but the preimage can be empty: n = 2, one letter σ with δ(σ, s1) = δ(σ, s2) = s1 (constant, hence monotonic), τ = σ, I = [s2, s2] gives δ−1(τ, I) = ∅; every later use applies the lemma to a nonempty preimage
--   - reading: δ monotonic: δ(σ, s1), …, δ(σ, sn), after removal of adjacent duplicate states, is a subsequence of a cyclic permutation of s1, …, sn → IsMonotonic (δ a) for every letter a: n = 0, or for some start m the cyclic offsets (δ a (m + i) − δ a m) mod n are nondecreasing in i; reason: 'adjacent' is read cyclically, as 'preserves the cyclic order' requires; this reading admits more automata than the linear one (s1→s1, s2→s2, s3→s1), so the statement is the stronger one; checked equal to the cyclic de-duplication reading for every map with n ≤ 6
--   - encoding: states s1, …, sn in cyclic order, letters σ1, …, σk, words in Σ∗ with δ(τ1τ2, s) = δ(τ2, δ(τ1, s)) → states Fin n with s_i = i − 1 and the cyclic order of Fin n, letters Fin k, words List (Fin k) read left to right (run = left fold); reason: relabelling; same instances
--   - encoding: interval [s_i, s_j] and the symbol ∞ → endpoint pair (i, j) : Fin n × Fin n with state set ivSet (i, j); ∞ is none in Option (Fin n × Fin n); reason: same objects; the n representations of S stay distinct pairs, as in the source
-- source:
--   Eppstein, Reset Sequences for Monotonic Automata, author manuscript of 7 Feb 1990 (SIAM J. Comput. 19, doi:10.1137/0219033; PDF sha256 6d8caa76…), p. 2 (PDF 3), Lemma 1

import Mathlib
import Definitions.Def_MonoReset_IntervalBFS_Model

namespace MonoReset.IntervalBFS

theorem lemma_1 {n k : ℕ} (δ : Fin k → Fin n → Fin n) (hδ : ∀ a, IsMonotonic (δ a))
    (τ : List (Fin k)) (I : Fin n × Fin n) :
    Finset.univ.filter (fun s => run δ τ s ∈ ivSet I) = ∅ ∨
      ∃ J : Fin n × Fin n, ivSet J = Finset.univ.filter (fun s => run δ τ s ∈ ivSet I) := by sorry

end MonoReset.IntervalBFS
