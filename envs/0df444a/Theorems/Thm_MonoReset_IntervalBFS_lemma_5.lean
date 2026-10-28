-- Prove2me | Theorems.Thm_MonoReset_IntervalBFS_lemma_5
-- name    : MonoReset.IntervalBFS.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:49.761757+00:00
-- url     : https://prove2.me/theorems/1d94997f-84a9-4806-aec3-df3e5d2e0e57
-- title:
--   Lemma 5, p. 4 — |δ(τ, X)| = 1 iff some interval representation I of δ⁻¹(τ, δ(τ, X)) has δ′(τ, I) ≠ ∞ and |δ′(τ, I)| = 1
-- statement:
--   Let $(S, \Sigma, \delta)$ be monotonic, $\tau \in \Sigma^*$ a word and $X \subseteq S$ any set of states (possibly empty). Then
--   $$|\delta(\tau, X)| = 1 \iff \exists\, I \text{ representing } \delta^{-1}(\tau, \delta(\tau, X)) \text{ as an interval with } \delta'(\tau, I) \ne \infty \text{ and } |\delta'(\tau, I)| = 1 .$$
--   Here $\delta^{-1}(\tau, Y) = \{s : \delta(\tau, s) \in Y\}$, and $|\delta'(\tau, I)| = 1$ means that the interval $\delta'(\tau, I)$ has exactly one state.
--
--   This is the paper's main lemma: reset sequences of $X$ in the original automaton are exactly the words that drive a suitable interval containing $X$ to a singleton interval in the interval automaton.
--
--   **Formalization Note** States are `Fin n`, with $s_i$ the element $i-1$ and the cyclic order $0 \to 1 \to \cdots \to n-1 \to 0$; letters are `Fin k`; a word is a list read left to right. An interval $[s_i, s_j]$ is its pair of endpoints, and ∞ is `none`. Monotonicity is read cyclically (see the definition item).
--
--   Differences from the source:
--   - reading: δ monotonic: δ(σ, s1), …, δ(σ, sn), after removal of adjacent duplicate states, is a subsequence of a cyclic permutation of s1, …, sn → IsMonotonic (δ a) for every letter a: n = 0, or for some start m the cyclic offsets (δ a (m + i) − δ a m) mod n are nondecreasing in i; reason: 'adjacent' is read cyclically, as 'preserves the cyclic order' requires; this reading admits more automata than the linear one (s1→s1, s2→s2, s3→s1), so the statement is the stronger one; checked equal to the cyclic de-duplication reading for every map with n ≤ 6
--   - encoding: states s1, …, sn in cyclic order, letters σ1, …, σk, words in Σ∗ with δ(τ1τ2, s) = δ(τ2, δ(τ1, s)) → states Fin n with s_i = i − 1 and the cyclic order of Fin n, letters Fin k, words List (Fin k) read left to right (run = left fold); reason: relabelling; same instances
--   - encoding: interval [s_i, s_j] and the symbol ∞ → endpoint pair (i, j) : Fin n × Fin n with state set ivSet (i, j); ∞ is none in Option (Fin n × Fin n); reason: same objects; the n representations of S stay distinct pairs, as in the source
-- source:
--   Eppstein, Reset Sequences for Monotonic Automata, author manuscript of 7 Feb 1990 (SIAM J. Comput. 19, doi:10.1137/0219033; PDF sha256 6d8caa76…), p. 4 (PDF 5), Lemma 5

import Mathlib
import Definitions.Def_MonoReset_IntervalBFS_Model

namespace MonoReset.IntervalBFS

theorem lemma_5 {n k : ℕ} (δ : Fin k → Fin n → Fin n) (hδ : ∀ a, IsMonotonic (δ a))
    (τ : List (Fin k)) (X : Finset (Fin n)) :
    IsResetSeq δ X τ ↔
      ∃ I : Fin n × Fin n,
        ivSet I = Finset.univ.filter (fun s => run δ τ s ∈ X.image (run δ τ)) ∧
        ∃ J : Fin n × Fin n, dPrime δ τ (some I) = some J ∧ (ivSet J).card = 1 := by sorry

end MonoReset.IntervalBFS
