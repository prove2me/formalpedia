-- Prove2me | Theorems.Thm_MonoReset_IntervalBFS_bfs_layers
-- name    : MonoReset.IntervalBFS.bfs_layers
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:10.860989+00:00
-- url     : https://prove2.me/theorems/c0c3c41c-ed40-4037-a141-0eb3cf82f5de
-- title:
--   Proof of Theorem 1, p. 4 — layer d of the breadth-first search is the set of intervals at δ′-distance exactly d from the minimal intervals
-- statement:
--   Let $(S, \Sigma, \delta)$ be any automaton (monotonicity is not needed) and $X \subseteq S$. Consider the breadth-first search of the algorithm: layer $0$ is the set of minimal intervals containing $X$, and layer $d+1$ consists of the intervals $\delta'(\sigma, I) \ne \infty$, computed by the table-based evaluation, for $I$ in layer $d$ and $\sigma \in \Sigma$, that lie in no earlier layer. Then for every $d \ge 0$ and every interval $I$,
--   $$I \in L_d \iff \min\{|\tau| : \tau \in \Sigma^*,\ \tau \text{ leads some minimal interval to } I\} = d,$$
--   i.e. some word of length $d$ leads a minimal interval containing $X$ to $I$, and no shorter word does. Here "$\tau$ leads $I_0$ to $I$" means that applying the table-based transitions letter by letter from $I_0$ ends at $I$ (never at $\infty$).
--
--   This is the correctness of "the standard breadth first search algorithm" in the proof of Theorem 1: the first layer containing a singleton interval is at the minimum distance of any singleton.
--
--   **Formalization Note** States are `Fin n`, with $s_i$ the element $i-1$ and the cyclic order $0 \to 1 \to \cdots \to n-1 \to 0$; letters are `Fin k`; a word is a list read left to right. An interval $[s_i, s_j]$ is its pair of endpoints, and ∞ is `none`. Monotonicity is read cyclically (see the definition item).
--
--   Differences from the source:
--   - reading: the shortest path from one of these intervals to a singleton can be found using the standard breadth first search algorithm → for all d and I: I ∈ (layers δ X d).1 ↔ some word of length d leads a minimal interval to I under dPrimeFast, and every word that does has length ≥ d; reason: the claim about the standard algorithm is stated as the layer invariant of the layered search the goal runs, which is what yields the shortest path
--   - encoding: transitions of the interval automaton δ′ → the table-based evaluation dPrimeFast; reason: the algorithm evaluates δ′ through the preimage table; the preimage-test milestone shows dPrimeFast = dPrime1 for monotonic letters
--   - encoding: states s1, …, sn in cyclic order, letters σ1, …, σk, words in Σ∗ with δ(τ1τ2, s) = δ(τ2, δ(τ1, s)) → states Fin n with s_i = i − 1 and the cyclic order of Fin n, letters Fin k, words List (Fin k) read left to right (run = left fold); reason: relabelling; same instances
--   - encoding: interval [s_i, s_j] and the symbol ∞ → endpoint pair (i, j) : Fin n × Fin n with state set ivSet (i, j); ∞ is none in Option (Fin n × Fin n); reason: same objects; the n representations of S stay distinct pairs, as in the source
--   - generalization: the breadth-first search runs on the monotonic automaton of Theorem 1 (standing assumption of the section, p. 2) → no monotonicity hypothesis: the layer invariant is stated for every transition function δ; reason: the layer invariant is a property of the layered search alone; it specializes to the source's monotonic automata
-- source:
--   Eppstein, Reset Sequences for Monotonic Automata, author manuscript of 7 Feb 1990 (SIAM J. Comput. 19, doi:10.1137/0219033; PDF sha256 6d8caa76…), p. 4 (PDF 5), proof of Theorem 1 ("Finally, the shortest path from one of these intervals to a singleton can be found using the standard breadth first search algorithm.")

import Mathlib
import Definitions.Def_MonoReset_IntervalBFS_Model
import Definitions.Def_MonoReset_IntervalBFS_Algorithm

namespace MonoReset.IntervalBFS

theorem bfs_layers {n k : ℕ} (δ : Fin k → Fin n → Fin n) (X : Finset (Fin n)) (d : ℕ)
    (I : Fin n × Fin n) :
    I ∈ (layers δ X d).1 ↔
      (∃ τ : List (Fin k), τ.length = d ∧
          ∃ I₀ ∈ minIntervals X, τ.foldl (fun J a => dPrimeFast δ a J) (some I₀) = some I) ∧
      ∀ τ : List (Fin k),
        (∃ I₀ ∈ minIntervals X, τ.foldl (fun J a => dPrimeFast δ a J) (some I₀) = some I) →
          d ≤ τ.length := by sorry

end MonoReset.IntervalBFS
