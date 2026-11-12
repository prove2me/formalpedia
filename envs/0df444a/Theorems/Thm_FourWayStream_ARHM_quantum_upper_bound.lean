-- Prove2me | Theorems.Thm_FourWayStream_ARHM_quantum_upper_bound
-- name    : FourWayStream.ARHM.quantum_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:41:54.194305+00:00
-- url     : https://prove2.me/theorems/0ac89617-8d27-414e-b31c-ac59d6b1ce36
-- title:
--   Proposition 5.7 — quantum random-order upper bound $O(\log N\log m)$
-- statement:
--   **Proposition 5.7 (Quantum random-order upper bound).** For every even $N$ and $2\le m\le\lfloor\sqrt N\rfloor$,
--   $$S^Q_{\mathrm{rand},1/3}(\mathrm{ARHM}_{N,m})=O(\log N\log m).$$
--   Precisely: there is a universal constant $C$ such that for every even $N$, every $2\le m\le\lfloor\sqrt N\rfloor$ and every one-factorization $F$ of $K_N$ there is a quantum streaming algorithm for $\mathrm{ARHM}_{N,m}$ with $L=(100m)^2$ copies whose instruments depend only on the item (the stage enters only through its memory), which has error at most $1/3$ in random order, and whose space, workspace included, is at most $C\log_2N\log_2m$.
--
--   This is the upper half of the separation: quantum memory in random order rebuilds the phase states that the requests consume.
--
--   **Formalization Note** The paper's proof gives $2\lceil9\log(m+1)\rceil$ registers of $\lceil\log N\rceil$ qubits and only "$O(\log N)$" for counters and classical control, so the constant is existential, quantified before $N$, $m$ and $F$.
--
--   Differences from the source:
--   - reading: §4.2: a classical controller applies, for every item, a circuit from a fixed finite set of gates and measurement operators to an array of qubits → every item is processed by an arbitrary quantum instrument (finite complete Kraus family indexed by the output) on the memory C^d; the finite gate set is not modelled; reason: §4.2 is ambiguous: it states that the lower bounds hold for arbitrary channels, and the paper's own algorithm (Prop 5.7) uses exact phases e^{iπ/µ} and exact Fourier and matching-basis measurements, which are not circuits over a fixed finite gate set
--   - reading: §4.2: live memory includes all workspace, and computing the fixed one-factorization is counted → upper-bound space = ⌈log₂ d⌉ (memory) + ⌈log₂(|Output|·r)⌉ (an ancilla holding the instrument outcome, Stinespring dilation); instruments may depend on F, whose computation is not charged; reason: with instruments as the primitive steps (reading above) the dilation ancilla is the workspace of a step; the paper bounds the cost of computing F only "for an explicit one-factorization"
--   - encoding: S^Q_{rand,1/3}(ARHM_{N,m}) = O(log N log m) → ∃ C : ℝ, chosen before N, m and F, and a stage-independent algorithm A with RandErrorLE F (1/3) and upperSpace A ≤ C · log₂ N · log₂ m; reason: the O-constant is universal; the minimum space S is bounded by exhibiting one algorithm
--   - encoding: random order: a uniformly random permutation of the NL + m labeled items → the average over all bijections Fin (N·L + m) ≃ (Fin N × Fin L) ⊕ Fin m (positions to labeled occurrences); reason: the uniform distribution on these bijections is the uniform random permutation of the labeled occurrences
--   - encoding: [N], [L], [m], [N − 1], edges {u, v}, bits in {0,1} → Fin N, Fin L, Fin m, Fin (N − 1) (0-based), Sym2 (Fin N), Bool with xor; reason: relabelling; no instance changes
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §5.1, p.22, Proposition 5.7

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM

/-- Proposition 5.7 (Quantum random-order upper bound), p.22. There is a universal constant `C`
such that for every even `N`, every `2 ≤ m ≤ ⌊√N⌋` and every one-factorization `F` of `K_N`, some
quantum streaming algorithm for `ARHM_{N,m}` (`L = (100m)²`), whose instruments depend only on the
item (stage only through memory), has error at most `1/3` in random order and space, workspace
included, at most `C log N log m`. -/
theorem quantum_upper_bound :
    ∃ C : ℝ, ∀ N m : ℕ, Even N → 2 ≤ m → m ≤ Nat.sqrt N →
      ∀ F : Fin (N - 1) → Finset (Sym2 (Fin N)), IsOneFactorization F →
        ∃ A : QStreamAlg N m ((100 * m) ^ 2), A.Valid ∧ A.StageIndependent ∧
          A.RandErrorLE F (1 / 3) ∧ (A.upperSpace : ℝ) ≤ C * Real.logb 2 N * Real.logb 2 m := by sorry

end FourWayStream.ARHM
