-- Prove2me | Theorems.Thm_MonoReset_IntervalBFS_minimal_interval_reduction
-- name    : MonoReset.IntervalBFS.minimal_interval_reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:16.628157+00:00
-- url     : https://prove2.me/theorems/ed33ab45-81eb-4fc2-8c0d-acf6eeb07d4c
-- title:
--   Proof of Theorem 1, p. 4 — τ resets X iff δ′(τ, ·) sends one of the minimal intervals [s_{i_j}, s_{i_{j−1}}] containing X to a singleton
-- statement:
--   Let $(S, \Sigma, \delta)$ be monotonic and $X = \{s_{i_1}, s_{i_2}, \dots\} \subseteq S$, listed in cyclic order. The **minimal intervals containing $X$** are the intervals $[s_{i_j}, s_{i_{j-1}}]$ (indices of $X$ taken cyclically), i.e. the intervals with both endpoints in $X$ that contain $X$. For every word $\tau \in \Sigma^*$,
--   $$|\delta(\tau, X)| = 1 \iff \exists\, I \text{ minimal interval containing } X,\ \exists\, s \in S:\ \delta'(\tau, I) = [s, s].$$
--
--   In particular the minimum length of a reset sequence of $X$ equals the minimum length of a path in the interval automaton from a minimal interval containing $X$ to a singleton interval, which is what the breadth-first search computes. For $X = \emptyset$ both sides are false.
--
--   **Formalization Note** States are `Fin n`, with $s_i$ the element $i-1$ and the cyclic order $0 \to 1 \to \cdots \to n-1 \to 0$; letters are `Fin k`; a word is a list read left to right. An interval $[s_i, s_j]$ is its pair of endpoints, and ∞ is `none`. Monotonicity is read cyclically (see the definition item).
--
--   Differences from the source:
--   - generalization: a minimum reset sequence is a minimum length path from some interval containing X to a singleton interval, and vice versa; only the minimal intervals [s_{i_j}, s_{i_{j−1}}] need be considered → for every word τ: IsResetSeq δ X τ ↔ ∃ I ∈ minIntervals X, ∃ s, dPrime δ τ (some I) = some (s, s); reason: the per-word equivalence implies the source's equality of minimum lengths (and its 'vice versa') by taking minima on both sides
--   - encoding: minimal intervals [s_{i_j}, s_{i_{j−1}}] for X = {s_{i_1}, s_{i_2}, …} → minIntervals X = pairs (x, y) ∈ X × X with X ⊆ ivSet (x, y); reason: for x ∈ X the only y ∈ X with X ⊆ [x, y] is the cyclic predecessor of x in X, so the two sets coincide; for X = {x} both are {[x, x]}
--   - reading: δ monotonic: δ(σ, s1), …, δ(σ, sn), after removal of adjacent duplicate states, is a subsequence of a cyclic permutation of s1, …, sn → IsMonotonic (δ a) for every letter a: n = 0, or for some start m the cyclic offsets (δ a (m + i) − δ a m) mod n are nondecreasing in i; reason: 'adjacent' is read cyclically, as 'preserves the cyclic order' requires; this reading admits more automata than the linear one (s1→s1, s2→s2, s3→s1), so the statement is the stronger one; checked equal to the cyclic de-duplication reading for every map with n ≤ 6
--   - encoding: states s1, …, sn in cyclic order, letters σ1, …, σk, words in Σ∗ with δ(τ1τ2, s) = δ(τ2, δ(τ1, s)) → states Fin n with s_i = i − 1 and the cyclic order of Fin n, letters Fin k, words List (Fin k) read left to right (run = left fold); reason: relabelling; same instances
--   - encoding: interval [s_i, s_j] and the symbol ∞ → endpoint pair (i, j) : Fin n × Fin n with state set ivSet (i, j); ∞ is none in Option (Fin n × Fin n); reason: same objects; the n representations of S stay distinct pairs, as in the source
-- source:
--   Eppstein, Reset Sequences for Monotonic Automata, author manuscript of 7 Feb 1990 (SIAM J. Comput. 19, doi:10.1137/0219033; PDF sha256 6d8caa76…), p. 4 (PDF 5), proof of Theorem 1 ("By lemma 5, … and vice versa. By lemma 3, … these minimal intervals can be found as [s_{i_j}, s_{i_{j−1}}].")

import Mathlib
import Definitions.Def_MonoReset_IntervalBFS_Model
import Definitions.Def_MonoReset_IntervalBFS_Algorithm

namespace MonoReset.IntervalBFS

theorem minimal_interval_reduction {n k : ℕ} (δ : Fin k → Fin n → Fin n)
    (hδ : ∀ a, IsMonotonic (δ a)) (X : Finset (Fin n)) (τ : List (Fin k)) :
    IsResetSeq δ X τ ↔ ∃ I ∈ minIntervals X, ∃ s : Fin n, dPrime δ τ (some I) = some (s, s) := by sorry

end MonoReset.IntervalBFS
