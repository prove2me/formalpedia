-- Prove2me | Theorems.Thm_MonoReset_IntervalBFS_lemma_3
-- name    : MonoReset.IntervalBFS.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:47.142283+00:00
-- url     : https://prove2.me/theorems/eb126db4-f2f5-479c-895f-4ddb03bb0050
-- title:
--   Lemma 3, p. 3 — if δ′(τ, I) ≠ ∞ then every J ≺ I has δ′(τ, J) ≠ ∞ and δ′(τ, J) ≺ δ′(τ, I)
-- statement:
--   Let $(S, \Sigma, \delta)$ be monotonic. For every word $\tau \in \Sigma^*$ and every interval $I$ with $\delta'(\tau, I) = I' \ne \infty$, and every interval $J \prec I$,
--   $$\delta'(\tau, J) \ne \infty \quad\text{and}\quad \delta'(\tau, J) \prec I' .$$
--   Here $J = [s_h, s_i] \prec I = [s_g, s_j]$ means that the endpoints appear in the cyclic order $s_g, s_h, s_i, s_j$.
--
--   The lemma lets the search start only from the minimal intervals containing $X$ instead of all intervals containing $X$, and it closes the induction in Lemma 5.
--
--   **Formalization Note** States are `Fin n`, with $s_i$ the element $i-1$ and the cyclic order $0 \to 1 \to \cdots \to n-1 \to 0$; letters are `Fin k`; a word is a list read left to right. An interval $[s_i, s_j]$ is its pair of endpoints, and ∞ is `none`. Monotonicity is read cyclically (see the definition item).
--
--   Differences from the source:
--   - reading: δ monotonic: δ(σ, s1), …, δ(σ, sn), after removal of adjacent duplicate states, is a subsequence of a cyclic permutation of s1, …, sn → IsMonotonic (δ a) for every letter a: n = 0, or for some start m the cyclic offsets (δ a (m + i) − δ a m) mod n are nondecreasing in i; reason: 'adjacent' is read cyclically, as 'preserves the cyclic order' requires; this reading admits more automata than the linear one (s1→s1, s2→s2, s3→s1), so the statement is the stronger one; checked equal to the cyclic de-duplication reading for every map with n ≤ 6
--   - encoding: states s1, …, sn in cyclic order, letters σ1, …, σk, words in Σ∗ with δ(τ1τ2, s) = δ(τ2, δ(τ1, s)) → states Fin n with s_i = i − 1 and the cyclic order of Fin n, letters Fin k, words List (Fin k) read left to right (run = left fold); reason: relabelling; same instances
--   - encoding: interval [s_i, s_j] and the symbol ∞ → endpoint pair (i, j) : Fin n × Fin n with state set ivSet (i, j); ∞ is none in Option (Fin n × Fin n); reason: same objects; the n representations of S stay distinct pairs, as in the source
--   - reading: J ≺ I: the endpoints of the intervals appear in the cyclic order s_g, s_h, s_i, s_j → Prec J I: (J.1 − I.1) mod n ≤ (J.2 − I.1) mod n ≤ (I.2 − I.1) mod n, i.e. the weak cyclic order I.1, J.1, J.2, I.2 within one turn from I.1 (coinciding endpoints allowed); reason: the order must be weak: a singleton [s_h, s_h] and J = I itself have coinciding endpoints, and the paper applies ≺ to them (Lemma 4 with δ′(σ, I) = J, the proof of Lemma 5 with [s_i, s_j] ≺ J); a representation of S is ≺ only the representation of S with the same first endpoint, as the source's remark on set versus interval containment says
-- source:
--   Eppstein, Reset Sequences for Monotonic Automata, author manuscript of 7 Feb 1990 (SIAM J. Comput. 19, doi:10.1137/0219033; PDF sha256 6d8caa76…), p. 3 (PDF 4), Lemma 3

import Mathlib
import Definitions.Def_MonoReset_IntervalBFS_Model

namespace MonoReset.IntervalBFS

theorem lemma_3 {n k : ℕ} (δ : Fin k → Fin n → Fin n) (hδ : ∀ a, IsMonotonic (δ a))
    (τ : List (Fin k)) (I I' : Fin n × Fin n) (hI : dPrime δ τ (some I) = some I')
    (J : Fin n × Fin n) (hJI : Prec J I) :
    ∃ J' : Fin n × Fin n, dPrime δ τ (some J) = some J' ∧ Prec J' I' := by sorry

end MonoReset.IntervalBFS
