-- Prove2me | Theorems.Thm_FourWayStream_ARHM_Supplement_quantum_random_order_ngc
-- name    : FourWayStream.ARHM.Supplement.quantum_random_order_ngc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:07:44.040198+00:00
-- url     : https://prove2.me/theorems/92ddc211-4bb7-4d99-8303-2bb1fc628e79
-- title:
--   Theorem 7.3 — quantum random-order Noisy Gap Cycle needs $\Omega(n)$ space for $k\ge1600\log n$
-- statement:
--   Under the conditions of Theorem 7.2 — $(n,k)$ admissible, $n$ sufficiently large and $k\ge1600\log_2n$ — every one-pass quantum streaming algorithm solving $\mathrm{NGC}_{n,k}$ with error at most $1/3$ in uniformly random edge order (on every promise graph, averaged over the order and the algorithm's randomness and measurements) uses
--   $$\Omega(n)$$
--   space: there are universal $c>0$ and $n_0$ with space at least $cn$ whenever $n\ge n_0$.
--
--   So for long cycles random order and quantum memory together give no saving over the trivial algorithm.
--
--   Differences from the source:
--   - reading: §4.2: a classical controller applies, for every item, a circuit from a fixed finite set of gates and measurement operators → every item is processed by an arbitrary quantum instrument (finite complete Kraus family) on the memory C^d; the finite gate set is not modelled; reason: §4.2 is ambiguous: it states that the lower bounds hold for arbitrary channels ("they only use that the memory between two items is a state of the given number of qubits and bits"); this is the base mission's reading
--   - generalization: §4.2: a step may depend on the stage only through stored memory; space is the maximum live memory including workspace inside a step → lower bounds hold for algorithms whose instruments (transitions) may also depend on the stage, charging only the memory between two items (⌈log₂ d⌉ qubits, ⌈log₂ S⌉ bits); reason: a larger algorithm class and a smaller charge; the paper's algorithms are the stage-independent ones, whose memory between items is at most their space
--   - encoding: under the same conditions … Ω(n) space → ∃ c > 0 and n₀ (universal) such that n ≥ n₀, k ≥ 1600 log₂ n imply c·n ≤ ⌈log₂ d⌉; reason: the standard meaning of Ω/O with the constant and threshold quantified before every varying parameter, as §4 uses them
--   - encoding: [N], [m], [w], [r], [n], bits in {0,1}, edges {u, v} → Fin N, Fin m, Fin w, Fin r, Fin n (0-based), Bool, Sym2; reason: Lean convention; same instances
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), p.33, Theorem 7.3 (proof p.33)

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Supplement_NGC

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM.Supplement

open QAlgorithms
open scoped Matrix

/-- Theorem 7.3 (Quantum random-order Noisy Gap Cycle), p.33. There are universal `c > 0` and `n₀`
such that for every admissible `(n, k)` with `n ≥ n₀` and `k ≥ 1600 log₂ n`, every one-pass quantum
streaming algorithm solving `NGC_{n,k}` with error at most `1/3` in uniformly random edge order uses
at least `c n` qubits of memory. -/
theorem quantum_random_order_ngc :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n k : ℕ, Admissible n k → n₀ ≤ n →
      1600 * Real.logb 2 n ≤ k → ∀ A : QEdgeAlg (Fin n), A.Valid → A.RandErrorLE k (1 / 3) →
        c * n ≤ A.space := by sorry

end FourWayStream.ARHM.Supplement
