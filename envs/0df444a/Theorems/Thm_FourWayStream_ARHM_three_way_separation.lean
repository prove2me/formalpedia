-- Prove2me | Theorems.Thm_FourWayStream_ARHM_three_way_separation
-- name    : FourWayStream.ARHM.three_way_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:41:58.440195+00:00
-- url     : https://prove2.me/theorems/a750b54e-81a0-43e9-aaad-1dcbdd0cd8af
-- title:
--   Theorem 5.3 — three-way separation for ARHM: $O(\log N\log m)$ quantum random order, $\Omega(\sqrt N)$ classical random order, $\Omega(m)$ quantum data-first
-- statement:
--   **Theorem 5.3 (Three-way separation).** For every even $N$ and every $2\le m\le\lfloor\sqrt N\rfloor$, the stream $\mathrm{ARHM}_{N,m}$, of length $NL+m=\Theta(Nm^2)$, satisfies
--   $$S^Q_{\mathrm{rand},1/3}(\mathrm{ARHM}_{N,m})=O(\log N\log m),\qquad S^C_{\mathrm{rand},1/3}(\mathrm{ARHM}_{N,m})=\Omega(\sqrt N),\qquad S^Q_{\mathrm{data\text{-}first},1/3}(\mathrm{ARHM}_{N,m})=\Omega(m).$$
--   The two lower bounds hold for every number $L\ge1$ of copies of each coordinate.
--
--   Precisely, the statement has four parts:
--
--   1. with $L=(100m)^2$ the stream has $NL+m=10^4Nm^2+m$ items;
--   2. there is a universal constant $C$ such that for every even $N$, every $2\le m\le\lfloor\sqrt N\rfloor$ and every one-factorization $F$ some stage-independent quantum algorithm has error at most $1/3$ in random order and space, workspace included, at most $C\log_2N\log_2m$;
--   3. every classical algorithm with error at most $1/3$ in random order uses at least $\sqrt{N-1}/6-1$ bits;
--   4. every quantum algorithm with error at most $1/3$ in data-first order has at least $m/2-1$ qubits.
--
--   Quantum memory and random order together are exponentially stronger than either resource alone: in random order quantum beats classical exponentially (for $m=2$), and for quantum algorithms random order beats data-first order exponentially (for $m=\lfloor\sqrt N\rfloor$).
--
--   **Formalization Note** The lower bounds use the explicit constants of the paper's proofs (Proposition 5.12, p.24; Proposition 5.13 with $s=m$, p.24), which imply the printed $\Omega$-bounds; they hold even for algorithms whose steps may depend on the stage and with only the memory between items charged.
--
--   Differences from the source:
--   - reading: §4.2: a classical controller applies, for every item, a circuit from a fixed finite set of gates and measurement operators to an array of qubits → every item is processed by an arbitrary quantum instrument (finite complete Kraus family indexed by the output) on the memory C^d; the finite gate set is not modelled; reason: §4.2 is ambiguous: it states that the lower bounds hold for arbitrary channels, and the paper's own algorithm (Prop 5.7) uses exact phases e^{iπ/µ} and exact Fourier and matching-basis measurements, which are not circuits over a fixed finite gate set
--   - reading: §4.2: live memory includes all workspace, and computing the fixed one-factorization is counted → upper-bound space = ⌈log₂ d⌉ (memory) + ⌈log₂(|Output|·r)⌉ (an ancilla holding the instrument outcome, Stinespring dilation); instruments may depend on F, whose computation is not charged; reason: with instruments as the primitive steps (reading above) the dilation ancilla is the workspace of a step; the paper bounds the cost of computing F only "for an explicit one-factorization"
--   - generalization: §4.2: a step may depend on the stage only through stored memory, and space is the maximum live memory including workspace inside a step → lower bounds hold for algorithms whose instruments (transitions) may also depend on the stage, charging only the memory between two items (⌈log₂ d⌉ qubits, ⌈log₂ S⌉ bits); reason: a larger algorithm class and a smaller charge; the paper's algorithms are the stage-independent ones, whose memory between items is at most their space
--   - generalization: ARHM_{N,m} with L = (100m)² copies → every number L ≥ 1 of copies; reason: the paper's remark after Theorem 5.3 (p.19); L = (100m)² is a special case
--   - encoding: length NL + m = Θ(Nm²) → streamLength N m ((100m)²) = 10⁴·N·m² + m; reason: the exact value given in the proof of Theorem 5.3 (p.25); it implies Θ(Nm²)
--   - encoding: S^Q_{rand,1/3}(ARHM_{N,m}) = O(log N log m) → ∃ C : ℝ, chosen before N, m and F, and a stage-independent algorithm A with RandErrorLE F (1/3) and upperSpace A ≤ C · log₂ N · log₂ m; reason: the O-constant is universal; the minimum space S is bounded by exhibiting one algorithm
--   - encoding: S^C_{rand,1/3}(ARHM_{N,m}) = Ω(√N) → √(N − 1)/6 − 1 ≤ ⌈log₂ S⌉ for every classical algorithm with error at most 1/3 in random order; reason: the explicit bound of the proof of Prop 5.12 (p.24: "Lemma 5.11 gives c ≥ √(N−1)/6 − 1"); it implies the Ω-bound, and a lower bound on the minimum is a bound for every algorithm
--   - encoding: S^Q_{data-first,1/3}(ARHM_{N,m}) = Ω(m) → m/2 − 1 ≤ ⌈log₂ d⌉ for every quantum algorithm with error at most 1/3 in data-first order; reason: the explicit bound of Prop 5.13 with s = m (p.24) and Cor 6.13 (p.32); it implies the Ω-bound
--   - encoding: random order: a uniformly random permutation of the NL + m labeled items → the average over all bijections Fin (N·L + m) ≃ (Fin N × Fin L) ⊕ Fin m (positions to labeled occurrences); reason: the uniform distribution on these bijections is the uniform random permutation of the labeled occurrences
--   - encoding: [N], [L], [m], [N − 1], edges {u, v}, bits in {0,1} → Fin N, Fin L, Fin m, Fin (N − 1) (0-based), Sym2 (Fin N), Bool with xor; reason: relabelling; no instance changes
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §5, p.19, Theorem 5.3 (proof p.25)

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM

/-- Theorem 5.3 (Three-way separation), p.19. For every even `N` and every `2 ≤ m ≤ ⌊√N⌋`:
(a) the stream `ARHM_{N,m}` with `L = (100m)²` has length `NL + m = 10⁴ N m² + m = Θ(N m²)`;
(b) `S^Q_{rand,1/3}(ARHM_{N,m}) = O(log N log m)`: a universal `C`, chosen before `N`, `m` and the
one-factorization, bounds the space (workspace included) of a stage-independent quantum algorithm
with error at most `1/3` in random order;
(c) `S^C_{rand,1/3}(ARHM_{N,m}) = Ω(√N)`: every classical algorithm with error at most `1/3` in random
order uses at least `√(N − 1)/6 − 1` bits, for every number `L ≥ 1` of copies;
(d) `S^Q_{data-first,1/3}(ARHM_{N,m}) = Ω(m)`: every quantum algorithm with error at most `1/3` in
data-first order has at least `m/2 − 1` qubits, for every `L ≥ 1`.
The lower bounds hold for algorithms whose steps may depend on the stage. -/
theorem three_way_separation :
    (∀ N m : ℕ, Even N → 2 ≤ m → m ≤ Nat.sqrt N →
      streamLength N m ((100 * m) ^ 2) = 10 ^ 4 * N * m ^ 2 + m) ∧
    (∃ C : ℝ, ∀ N m : ℕ, Even N → 2 ≤ m → m ≤ Nat.sqrt N →
      ∀ F : Fin (N - 1) → Finset (Sym2 (Fin N)), IsOneFactorization F →
        ∃ A : QStreamAlg N m ((100 * m) ^ 2), A.Valid ∧ A.StageIndependent ∧
          A.RandErrorLE F (1 / 3) ∧ (A.upperSpace : ℝ) ≤ C * Real.logb 2 N * Real.logb 2 m) ∧
    (∀ N m L : ℕ, Even N → 2 ≤ m → m ≤ Nat.sqrt N → 1 ≤ L →
      ∀ F : Fin (N - 1) → Finset (Sym2 (Fin N)), IsOneFactorization F →
        ∀ A : CStreamAlg N m L, A.Valid → A.RandErrorLE F (1 / 3) →
          Real.sqrt ((N : ℝ) - 1) / 6 - 1 ≤ A.space) ∧
    (∀ N m L : ℕ, Even N → 2 ≤ m → m ≤ Nat.sqrt N → 1 ≤ L →
      ∀ F : Fin (N - 1) → Finset (Sym2 (Fin N)), IsOneFactorization F →
        ∀ A : QStreamAlg N m L, A.Valid → A.DataFirstErrorLE F (1 / 3) →
          (m : ℝ) / 2 - 1 ≤ A.space) := by sorry

end FourWayStream.ARHM
