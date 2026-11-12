-- Prove2me | Theorems.Thm_FourWayStream_ARHM_classical_random_order_lower_bound
-- name    : FourWayStream.ARHM.classical_random_order_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:42:03.62302+00:00
-- url     : https://prove2.me/theorems/d9b6080c-7e8a-496d-847c-839124c43573
-- title:
--   Proposition 5.12 — classical random-order lower bound $\sqrt{N-1}/6-1$
-- statement:
--   **Proposition 5.12 (Classical random-order lower bound).** For every even $N$, every number $m\ge1$ of requests and every number $L\ge1$ of copies, every classical streaming algorithm for $\mathrm{ARHM}_{N,m}$ with error at most $1/3$ in random order uses at least
--   $$\frac{\sqrt{N-1}}{6}-1$$
--   bits of memory. Hence $S^C_{\mathrm{rand},1/3}(\mathrm{ARHM}_{N,m})=\Omega(\sqrt N)$.
--
--   This is the classical half of the separation in random order.
--
--   Differences from the source:
--   - generalization: §4.2: a step may depend on the stage only through stored memory, and space is the maximum live memory including workspace inside a step → lower bounds hold for algorithms whose instruments (transitions) may also depend on the stage, charging only the memory between two items (⌈log₂ d⌉ qubits, ⌈log₂ S⌉ bits); reason: a larger algorithm class and a smaller charge; the paper's algorithms are the stage-independent ones, whose memory between items is at most their space
--   - reading: "For every m" → every m ≥ 1 (including m = 1 and m > ⌊√N⌋); reason: with m = 0 there is no request and no lower bound holds; the proof uses the first request only
--   - encoding: S^C_{rand,1/3}(ARHM_{N,m}) = Ω(√N) → √(N − 1)/6 − 1 ≤ ⌈log₂ S⌉ for every classical algorithm with error at most 1/3 in random order; reason: the explicit bound of the proof (p.24: "Lemma 5.11 gives c ≥ √(N−1)/6 − 1"); it implies the Ω-bound
--   - encoding: random order: a uniformly random permutation of the NL + m labeled items → the average over all bijections Fin (N·L + m) ≃ (Fin N × Fin L) ⊕ Fin m (positions to labeled occurrences); reason: the uniform distribution on these bijections is the uniform random permutation of the labeled occurrences
--   - encoding: [N], [L], [m], [N − 1], edges {u, v}, bits in {0,1} → Fin N, Fin L, Fin m, Fin (N − 1) (0-based), Sym2 (Fin N), Bool with xor; reason: relabelling; no instance changes
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §5.2, p.24, Proposition 5.12 (explicit constant from its proof, p.24)

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM

/-- Proposition 5.12 (Classical random-order lower bound), p.24. For every even `N`, every number
`m ≥ 1` of requests and every number `L ≥ 1` of copies, every classical streaming algorithm for
`ARHM_{N,m}` with error at most `1/3` in random order uses at least `√(N − 1)/6 − 1` bits, so
`S^C_{rand,1/3}(ARHM_{N,m}) = Ω(√N)`. Steps may depend on the stage. -/
theorem classical_random_order_lower_bound (N m L : ℕ) (hN : Even N) (hm : 1 ≤ m) (hL : 1 ≤ L)
    (F : Fin (N - 1) → Finset (Sym2 (Fin N))) (hF : IsOneFactorization F)
    (A : CStreamAlg N m L) (hA : A.Valid) (herr : A.RandErrorLE F (1 / 3)) :
    Real.sqrt ((N : ℝ) - 1) / 6 - 1 ≤ A.space := by sorry

end FourWayStream.ARHM
