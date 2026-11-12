-- Prove2me | Theorems.Thm_FourWayStream_ARHM_data_first_lower_bound
-- name    : FourWayStream.ARHM.data_first_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:41:59.810195+00:00
-- url     : https://prove2.me/theorems/30c3bbb9-9535-4678-be7f-b508d9af2235
-- title:
--   Corollary 5.15 — data-first lower bound $m/2-1$
-- statement:
--   **Corollary 5.15 (Data-first lower bound).** For every even $N$, every $2\le m\le\lfloor\sqrt N\rfloor$ and every number $L\ge1$ of copies, every quantum streaming algorithm for $\mathrm{ARHM}_{N,m}$ with error at most $1/3$ in data-first order has at least
--   $$\frac m2-1$$
--   qubits of memory. Hence $S^Q_{\mathrm{data\text{-}first},1/3}(\mathrm{ARHM}_{N,m})=\Omega(m)$.
--
--   Without later data, quantum memory gives no exponential saving: this is the third clause of the separation.
--
--   Differences from the source:
--   - reading: §4.2: a classical controller applies, for every item, a circuit from a fixed finite set of gates and measurement operators to an array of qubits → every item is processed by an arbitrary quantum instrument (finite complete Kraus family indexed by the output) on the memory C^d; the finite gate set is not modelled; reason: §4.2 is ambiguous: it states that the lower bounds hold for arbitrary channels, and the paper's own algorithm (Prop 5.7) uses exact phases e^{iπ/µ} and exact Fourier and matching-basis measurements, which are not circuits over a fixed finite gate set
--   - generalization: §4.2: a step may depend on the stage only through stored memory, and space is the maximum live memory including workspace inside a step → lower bounds hold for algorithms whose instruments (transitions) may also depend on the stage, charging only the memory between two items (⌈log₂ d⌉ qubits, ⌈log₂ S⌉ bits); reason: a larger algorithm class and a smaller charge; the paper's algorithms are the stage-independent ones, whose memory between items is at most their space
--   - encoding: S^Q_{data-first,1/3}(ARHM_{N,m}) = Ω(m) → m/2 − 1 ≤ ⌈log₂ d⌉ for every quantum algorithm with error at most 1/3 in data-first order; reason: the explicit bound of Prop 5.13 with s = m; it implies the Ω-bound
--   - encoding: [N], [L], [m], [N − 1], edges {u, v}, bits in {0,1} → Fin N, Fin L, Fin m, Fin (N − 1) (0-based), Sym2 (Fin N), Bool with xor; reason: relabelling; no instance changes
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §5.3, p.25, Corollary 5.15 (explicit constant: Proposition 5.13 with s = m, p.24)

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM

/-- Corollary 5.15 (Data-first lower bound), p.25. For every even `N`, every `2 ≤ m ≤ ⌊√N⌋` and
every number `L ≥ 1` of copies, every quantum streaming algorithm for `ARHM_{N,m}` with error at most
`1/3` in data-first order has at least `m/2 − 1` qubits of memory, so
`S^Q_{data-first,1/3}(ARHM_{N,m}) = Ω(m)`. Steps may depend on the stage. -/
theorem data_first_lower_bound (N m L : ℕ) (hN : Even N) (hm : 2 ≤ m) (hmN : m ≤ Nat.sqrt N)
    (hL : 1 ≤ L) (F : Fin (N - 1) → Finset (Sym2 (Fin N))) (hF : IsOneFactorization F)
    (A : QStreamAlg N m L) (hA : A.Valid) (herr : A.DataFirstErrorLE F (1 / 3)) :
    (m : ℝ) / 2 - 1 ≤ A.space := by sorry

end FourWayStream.ARHM
