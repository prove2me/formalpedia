-- Prove2me | Theorems.Thm_MonoReset_IntervalBFS_dPrime_characterization
-- name    : MonoReset.IntervalBFS.dPrime_characterization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:45.283524+00:00
-- url     : https://prove2.me/theorems/803cdcbd-76f2-4678-8827-c7974ccb8e85
-- title:
--   δ′ on words, p. 3 — cases (1)–(3) of the interval transition hold for every input sequence τ, with ∞ possible in case (2)
-- statement:
--   Let $(S, \Sigma, \delta)$ be monotonic, let $\tau \in \Sigma^*$ be a word, let $I = [s_i, s_j]$ be an interval, and write $d_x = \delta(\tau, s_x)$. Then:
--
--   1. if $d_i \ne d_j$, then $\delta'(\tau, I) = [d_i, d_j]$;
--   2. if $d_i = d_{i+1} = \cdots = d_j$ (that is, $\delta(\tau, \cdot)$ is constant on $[s_i, s_j]$), then $\delta'(\tau, I) = [d_i, d_i]$ or $\delta'(\tau, I) = \infty$;
--   3. otherwise ($d_i = d_j$ but $\delta(\tau, \cdot)$ is not constant on $[s_i, s_j]$), $\delta'(\tau, I) = \infty$;
--
--   and $\delta'(\tau, \infty) = \infty$. In other words,
--   $$\delta'(\tau, [s_i, s_j]) \in \bigl\{[\delta(\tau, s_i), \delta(\tau, s_j)],\ \infty\bigr\},$$
--   with the first value forced when the endpoint images differ and the second forced when they coincide on a non-constant interval.
--
--   The defining rules of $\delta'$ for single letters thus persist along words, except that case (2) may now give $\infty$; Lemmas 2 and 3 are read off this characterization.
--
--   **Formalization Note** States are `Fin n`, with $s_i$ the element $i-1$ and the cyclic order $0 \to 1 \to \cdots \to n-1 \to 0$; letters are `Fin k`; a word is a list read left to right. An interval $[s_i, s_j]$ is its pair of endpoints, and ∞ is `none`. Monotonicity is read cyclically (see the definition item).
--
--   Differences from the source:
--   - reading: δ monotonic: δ(σ, s1), …, δ(σ, sn), after removal of adjacent duplicate states, is a subsequence of a cyclic permutation of s1, …, sn → IsMonotonic (δ a) for every letter a: n = 0, or for some start m the cyclic offsets (δ a (m + i) − δ a m) mod n are nondecreasing in i; reason: 'adjacent' is read cyclically, as 'preserves the cyclic order' requires; this reading admits more automata than the linear one (s1→s1, s2→s2, s3→s1), so the statement is the stronger one; checked equal to the cyclic de-duplication reading for every map with n ≤ 6
--   - encoding: states s1, …, sn in cyclic order, letters σ1, …, σk, words in Σ∗ with δ(τ1τ2, s) = δ(τ2, δ(τ1, s)) → states Fin n with s_i = i − 1 and the cyclic order of Fin n, letters Fin k, words List (Fin k) read left to right (run = left fold); reason: relabelling; same instances
--   - encoding: interval [s_i, s_j] and the symbol ∞ → endpoint pair (i, j) : Fin n × Fin n with state set ivSet (i, j); ∞ is none in Option (Fin n × Fin n); reason: same objects; the n representations of S stay distinct pairs, as in the source
-- source:
--   Eppstein, Reset Sequences for Monotonic Automata, author manuscript of 7 Feb 1990 (SIAM J. Comput. 19, doi:10.1137/0219033; PDF sha256 6d8caa76…), p. 3 (PDF 4), unnumbered characterization of δ′(τ, I) ("the following facts follow by an easy induction")

import Mathlib
import Definitions.Def_MonoReset_IntervalBFS_Model

namespace MonoReset.IntervalBFS

theorem dPrime_characterization {n k : ℕ} (δ : Fin k → Fin n → Fin n)
    (hδ : ∀ a, IsMonotonic (δ a)) (τ : List (Fin k)) (I : Fin n × Fin n) :
    (run δ τ I.1 ≠ run δ τ I.2 →
        dPrime δ τ (some I) = some (run δ τ I.1, run δ τ I.2)) ∧
    ((∀ s ∈ ivSet I, run δ τ s = run δ τ I.1) →
        dPrime δ τ (some I) = some (run δ τ I.1, run δ τ I.1) ∨ dPrime δ τ (some I) = none) ∧
    (run δ τ I.1 = run δ τ I.2 → ¬ (∀ s ∈ ivSet I, run δ τ s = run δ τ I.1) →
        dPrime δ τ (some I) = none) ∧
    dPrime δ τ none = none := by sorry

end MonoReset.IntervalBFS
