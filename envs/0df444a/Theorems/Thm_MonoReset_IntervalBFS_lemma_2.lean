-- Prove2me | Theorems.Thm_MonoReset_IntervalBFS_lemma_2
-- name    : MonoReset.IntervalBFS.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:42.495476+00:00
-- url     : https://prove2.me/theorems/61c94d64-121b-4adc-9a12-7a636bc320f2
-- title:
--   Lemma 2, p. 3 — if δ′(τ, I) ≠ ∞ then δ(τ, I) ⊆ δ′(τ, I)
-- statement:
--   Let $(S, \Sigma, \delta)$ be monotonic. For every word $\tau \in \Sigma^*$ and every interval $I$, if $\delta'(\tau, I) = J \ne \infty$ then
--   $$\delta(\tau, I) = \{\delta(\tau, s) : s \in I\} \subseteq J .$$
--
--   So the interval automaton over-approximates the image of an interval; this is the direction of Lemma 5 that turns a path to a singleton interval into a reset sequence.
--
--   **Formalization Note** States are `Fin n`, with $s_i$ the element $i-1$ and the cyclic order $0 \to 1 \to \cdots \to n-1 \to 0$; letters are `Fin k`; a word is a list read left to right. An interval $[s_i, s_j]$ is its pair of endpoints, and ∞ is `none`. Monotonicity is read cyclically (see the definition item).
--
--   Differences from the source:
--   - reading: δ(τ, I) ⊂ δ′(τ, I) → (ivSet I).image (run δ τ) ⊆ ivSet J; reason: the paper writes ⊂ for ⊆ throughout (e.g. X ⊂ S for an arbitrary set of initial states, p. 1)
--   - reading: δ monotonic: δ(σ, s1), …, δ(σ, sn), after removal of adjacent duplicate states, is a subsequence of a cyclic permutation of s1, …, sn → IsMonotonic (δ a) for every letter a: n = 0, or for some start m the cyclic offsets (δ a (m + i) − δ a m) mod n are nondecreasing in i; reason: 'adjacent' is read cyclically, as 'preserves the cyclic order' requires; this reading admits more automata than the linear one (s1→s1, s2→s2, s3→s1), so the statement is the stronger one; checked equal to the cyclic de-duplication reading for every map with n ≤ 6
--   - encoding: states s1, …, sn in cyclic order, letters σ1, …, σk, words in Σ∗ with δ(τ1τ2, s) = δ(τ2, δ(τ1, s)) → states Fin n with s_i = i − 1 and the cyclic order of Fin n, letters Fin k, words List (Fin k) read left to right (run = left fold); reason: relabelling; same instances
--   - encoding: interval [s_i, s_j] and the symbol ∞ → endpoint pair (i, j) : Fin n × Fin n with state set ivSet (i, j); ∞ is none in Option (Fin n × Fin n); reason: same objects; the n representations of S stay distinct pairs, as in the source
-- source:
--   Eppstein, Reset Sequences for Monotonic Automata, author manuscript of 7 Feb 1990 (SIAM J. Comput. 19, doi:10.1137/0219033; PDF sha256 6d8caa76…), p. 3 (PDF 4), Lemma 2

import Mathlib
import Definitions.Def_MonoReset_IntervalBFS_Model

namespace MonoReset.IntervalBFS

theorem lemma_2 {n k : ℕ} (δ : Fin k → Fin n → Fin n) (hδ : ∀ a, IsMonotonic (δ a))
    (τ : List (Fin k)) (I J : Fin n × Fin n) (hJ : dPrime δ τ (some I) = some J) :
    (ivSet I).image (run δ τ) ⊆ ivSet J := by sorry

end MonoReset.IntervalBFS
