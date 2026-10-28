-- Prove2me | Theorems.Thm_MonoReset_IntervalBFS_theorem_1
-- name    : MonoReset.IntervalBFS.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:16.813983+00:00
-- url     : https://prove2.me/theorems/ac0dfe6c-eb84-40f2-ac43-de0452aa179b
-- title:
--   Theorem 1, p. 4 — interval BFS returns a minimum-length reset sequence of X exactly when one exists, at counted cost ≤ 11·k·n²
-- statement:
--   Let $(S, \Sigma, \delta)$ be a monotonic automaton with $n$ states and $k$ letters, and let $X \subseteq S$ be any set of initial states. Run the algorithm of the definition item: build the preimage table, compute the minimal intervals containing $X$, run the breadth-first search over the interval automaton with the table-based evaluation of $\delta'$, stop at the first layer $D$ that contains a singleton interval or is empty, and output a word read off the parent pointers, or "none". Then:
--
--   1. **(decision)** the output is "none" if and only if $X$ has no reset sequence;
--   2. **(minimum length)** every output word $\tau$ is a reset sequence of $X$, $|\delta(\tau, X)| = 1$, and $|\tau| \le |\tau'|$ for every reset sequence $\tau' \in \Sigma^*$ of $X$;
--   3. **(time $O(kn^2)$)** if $k \ge 1$, the counted cost of the run satisfies
--   $$\mathrm{cost} \le 11\, k\, n^2 .$$
--
--   The cost counts $k n \cdot n$ units for the preimage table, one dequeue and one evaluation per letter (3 or 8 units) for every interval of every layer up to $D$, and $D$ units for the output word. This is Eppstein's improvement of Natarajan's $O(kn^4)$ algorithms, which did not guarantee a shortest sequence; the same search yields the length bound $n^2 - 2n + 1$ of Theorem 2.
--
--   **Formalization Note** States are `Fin n`, with $s_i$ the element $i-1$ and the cyclic order $0 \to 1 \to \cdots \to n-1 \to 0$; letters are `Fin k`; a word is a list read left to right. An interval $[s_i, s_j]$ is its pair of endpoints, and ∞ is `none`. Monotonicity is read cyclically (see the definition item).
--
--   Differences from the source:
--   - generalization: a minimum length reset sequence can be found (for X with a reset sequence) → bfsResult δ X = none ↔ no word resets X, together with the minimum-length clause for every returned word; reason: the abstract and p. 1–2 say the algorithm either produces a sequence or proves none exists; the decision clause adds this and specializes to the printed claim when a reset sequence exists
--   - generalization: initial states X = {s_{i_1}, s_{i_2}, …} → every X : Finset (Fin n), including X = ∅ (output none) and singletons (output the empty word); reason: covers the source's nonempty X; the degenerate sets are included rather than excluded
--   - generalization: time bounded by O(kn^2) → 0 < k → bfsCost δ X ≤ 11 * k * n ^ 2; reason: an explicit constant implies the O-bound; k ≥ 1 because Σ = {σ1, …, σk} is an alphabet, and at k = 0 any bound C·k·n² is 0 while the search still reads X
--   - encoding: time of the algorithm → bfsCost: k·n·n for the kn preimage intervals, (1 + Σ_a evalCost) per interval of each layer up to bfsStop with evalCost ∈ {3, 8}, plus bfsStop for the output; reason: no machine model is formalized; the cost is the source's own unit count, computed from the layers the run visits, not from n²
--   - reading: δ monotonic: δ(σ, s1), …, δ(σ, sn), after removal of adjacent duplicate states, is a subsequence of a cyclic permutation of s1, …, sn → IsMonotonic (δ a) for every letter a: n = 0, or for some start m the cyclic offsets (δ a (m + i) − δ a m) mod n are nondecreasing in i; reason: 'adjacent' is read cyclically, as 'preserves the cyclic order' requires; this reading admits more automata than the linear one (s1→s1, s2→s2, s3→s1), so the statement is the stronger one; checked equal to the cyclic de-duplication reading for every map with n ≤ 6
--   - encoding: states s1, …, sn in cyclic order, letters σ1, …, σk, words in Σ∗ with δ(τ1τ2, s) = δ(τ2, δ(τ1, s)) → states Fin n with s_i = i − 1 and the cyclic order of Fin n, letters Fin k, words List (Fin k) read left to right (run = left fold); reason: relabelling; same instances
--   - encoding: interval [s_i, s_j] and the symbol ∞ → endpoint pair (i, j) : Fin n × Fin n with state set ivSet (i, j); ∞ is none in Option (Fin n × Fin n); reason: same objects; the n representations of S stay distinct pairs, as in the source
-- source:
--   Eppstein, Reset Sequences for Monotonic Automata, author manuscript of 7 Feb 1990 (SIAM J. Comput. 19, doi:10.1137/0219033; PDF sha256 6d8caa76…), p. 4 (PDF 5), Theorem 1 and its proof; procedure and unit costs from p. 3 (PDF 4) and the proof of Theorem 2, p. 4 (PDF 5)

import Mathlib
import Definitions.Def_MonoReset_IntervalBFS_Model
import Definitions.Def_MonoReset_IntervalBFS_Algorithm

namespace MonoReset.IntervalBFS

theorem theorem_1 {n k : ℕ} (δ : Fin k → Fin n → Fin n) (hδ : ∀ a, IsMonotonic (δ a))
    (X : Finset (Fin n)) :
    (bfsResult δ X = none ↔ ∀ τ : List (Fin k), ¬ IsResetSeq δ X τ) ∧
    (∀ τ : List (Fin k), bfsResult δ X = some τ →
        IsResetSeq δ X τ ∧ ∀ τ' : List (Fin k), IsResetSeq δ X τ' → τ.length ≤ τ'.length) ∧
    (0 < k → bfsCost δ X ≤ 11 * k * n ^ 2) := by sorry

end MonoReset.IntervalBFS
