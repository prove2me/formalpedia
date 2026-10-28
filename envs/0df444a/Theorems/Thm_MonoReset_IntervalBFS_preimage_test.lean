-- Prove2me | Theorems.Thm_MonoReset_IntervalBFS_preimage_test
-- name    : MonoReset.IntervalBFS.preimage_test
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:25.07344+00:00
-- url     : https://prove2.me/theorems/3db0be43-4edd-4ea1-9831-ca90964ea1e5
-- title:
--   Preimage test, p. 3 (corrected: the preimage interval exists for s in the image) — the preimage-interval table evaluates δ′(σ, ·) exactly
-- statement:
--   Let $(S, \Sigma, \delta)$ be monotonic and $\sigma \in \Sigma$. Then:
--
--   1. for every state $s$ in the image of $\delta(\sigma, \cdot)$, the preimage $\delta^{-1}(\sigma, s)$ is an interval, so the preimage table stores an interval for $s$;
--   2. if $\sigma$ maps both endpoints of an interval $I$ to the same state $s$, then
--   $$\delta'(\sigma, I) \ne \infty \iff I \subseteq \delta^{-1}(\sigma, s) \quad\text{(as sets of states)};$$
--   3. the table-based evaluation of the algorithm (compare the endpoint images; if they coincide at $s$, look up the stored interval $P$ for $\delta^{-1}(\sigma, s)$ and answer $[s, s]$ exactly when $P$ represents $S$ or $I \prec P$) agrees with $\delta'(\sigma, \cdot)$ on every state of $S'$, $\infty$ included.
--
--   Clause 3 is the paper's claim that the set containment in clause 2 "can be calculated using a constant number of comparisons between interval endpoints to determine interval containment, together with a test for the special case that $\delta^{-1}(\sigma, s) = S$". It is what lets the breadth-first search evaluate each transition in constant time.
--
--   **Formalization Note** States are `Fin n`, with $s_i$ the element $i-1$ and the cyclic order $0 \to 1 \to \cdots \to n-1 \to 0$; letters are `Fin k`; a word is a list read left to right. An interval $[s_i, s_j]$ is its pair of endpoints, and ∞ is `none`. Monotonicity is read cyclically (see the definition item).
--
--   Differences from the source:
--   - correction: for each σ ∈ Σ and s ∈ S the interval δ−1(σ, s) must exist by Lemma 1 → preimTable δ a s ≠ none for every s in the image of δ a; reason: the preimage of a state outside the image is empty, not an interval (n = 2, δ(σ, ·) ≡ s1, s = s2); the table is only consulted at s = δ(σ, s_i), which lies in the image
--   - reading: the containment can be calculated using a constant number of endpoint comparisons together with a test for δ−1(σ, s) = S → dPrimeFast δ a = dPrime1 δ a, where dPrimeFast uses only the endpoint images, one table entry, the test (P.2 − P.1) mod n = n − 1 and the comparison I ≺ P; reason: the computational claim is stated as the equality of the constant-step evaluation with δ′; its unit charges are counted in the goal's bfsCost
--   - encoding: this construction takes time O(n) per interval, O(kn^2) in total → charged k·n·n units in bfsCost (definition item), bounded in the goal's cost clause; reason: no machine model is formalized; the time claim is the source's own unit count
--   - reading: δ monotonic: δ(σ, s1), …, δ(σ, sn), after removal of adjacent duplicate states, is a subsequence of a cyclic permutation of s1, …, sn → IsMonotonic (δ a) for every letter a: n = 0, or for some start m the cyclic offsets (δ a (m + i) − δ a m) mod n are nondecreasing in i; reason: 'adjacent' is read cyclically, as 'preserves the cyclic order' requires; this reading admits more automata than the linear one (s1→s1, s2→s2, s3→s1), so the statement is the stronger one; checked equal to the cyclic de-duplication reading for every map with n ≤ 6
--   - encoding: states s1, …, sn in cyclic order, letters σ1, …, σk, words in Σ∗ with δ(τ1τ2, s) = δ(τ2, δ(τ1, s)) → states Fin n with s_i = i − 1 and the cyclic order of Fin n, letters Fin k, words List (Fin k) read left to right (run = left fold); reason: relabelling; same instances
--   - encoding: interval [s_i, s_j] and the symbol ∞ → endpoint pair (i, j) : Fin n × Fin n with state set ivSet (i, j); ∞ is none in Option (Fin n × Fin n); reason: same objects; the n representations of S stay distinct pairs, as in the source
-- source:
--   Eppstein, Reset Sequences for Monotonic Automata, author manuscript of 7 Feb 1990 (SIAM J. Comput. 19, doi:10.1137/0219033; PDF sha256 6d8caa76…), p. 3 (PDF 4), unnumbered (construction of δ′ from the preimage intervals δ−1(σ, s))

import Mathlib
import Definitions.Def_MonoReset_IntervalBFS_Model
import Definitions.Def_MonoReset_IntervalBFS_Algorithm

namespace MonoReset.IntervalBFS

theorem preimage_test {n k : ℕ} (δ : Fin k → Fin n → Fin n) (hδ : ∀ a, IsMonotonic (δ a))
    (a : Fin k) :
    (∀ s : Fin n, (∃ x, δ a x = s) → preimTable δ a s ≠ none) ∧
    (∀ I : Fin n × Fin n, δ a I.1 = δ a I.2 →
        (dPrime1 δ a (some I) ≠ none ↔
          ivSet I ⊆ Finset.univ.filter (fun x => δ a x = δ a I.1))) ∧
    dPrimeFast δ a = dPrime1 δ a := by sorry

end MonoReset.IntervalBFS
