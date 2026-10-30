-- Prove2me | Theorems.Thm_MITMSynthesis_mitm_factor_main
-- name    : MITMSynthesis.mitm_factor_main
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:11:02.962738+00:00
-- url     : https://prove2.me/theorems/336e2b50-b7b7-44df-bf01-8912b94cd5d1
-- title:
--   Main result: depth-optimal synthesis in $O(|V_{n,\mathcal G}|^{\lceil l/2\rceil}\log|V_{n,\mathcal G}|^{\lceil l/2\rceil})$ time (corrected: no depth-(l+1) test, depth-0 test, nondegenerate cost)
-- statement:
--   There is an absolute constant $C$ such that the following holds for every number of qubits $n$, every instruction set $\mathcal G$ (closed under inverses), every duplicate-free list `vs` of (layer, unitary) pairs enumerating $V_{n,\mathcal G}$, every linear order on $2^n\times 2^n$ matrices, every unitary $U \in U(2^n)$ and every depth bound $l \in \mathbb N$. Let $S_m$ be the set of unitaries implementable in depth $m$ over $\mathcal G$, and run MITM-factor (corrected) on `vs`, $U$, $l$ in the RAM model.
--
--   1. **(decision)** It returns a circuit if and only if $U$ can be implemented over $\mathcal G$ in depth at most $l$:
--   $$
--   \text{MITM-factor returns a circuit} \iff \exists\, m \le l,\ U \in S_m .
--   $$
--   2. **(minimal-depth synthesis)** If it returns a circuit $L_1, \dots, L_k$, then every $L_j$ is a layer over $\mathcal G$, $U_1U_2\cdots U_k = U$ for their unitaries, and $k$ is the minimal depth of $U$ over $\mathcal G$.
--   3. **(running time)** If $|V_{n,\mathcal G}| \ge 2$ and $l \ge 1$, the number of unit-cost steps is at most
--   $$
--   C \cdot |V_{n,\mathcal G}|^{\lceil l/2\rceil} \cdot \log\bigl(|V_{n,\mathcal G}|^{\lceil l/2\rceil}\bigr).
--   $$
--
--   This is the paper's main result: a meet-in-the-middle search that decides depth-$\le l$ implementability and synthesizes a depth-optimal circuit in time roughly the square root of the $O(|V_{n,\mathcal G}|^l)$ brute-force search.
--
--   **Formalization Note** The unit-cost steps are counted by the cost monad `Timed`: one step per multiplication, adjoint or comparison of unitaries and per list or array step; the cost bound is about the same run whose result clauses 1 and 2 describe. $\lceil l/2\rceil$ is `(l + 1) / 2` and $|V_{n,\mathcal G}|$ is `Set.ncard`.
--
--   Differences from the source:
--   - correction: the loop tests S_i†U ∩ S_i ≠ ∅ (depth 2i) in every iteration i ≤ ⌈l/2⌉, so for odd l it tests depth l+1 → depth 2i is tested only when 2i ≤ l; reason: counterexample: n = 1, G = {T, T†}, V_{n,G} = {T, T†}, U = P = T², l = 1: the printed algorithm returns the circuit TT of depth 2 > l although P ∉ S_0 ∪ S_1, so it neither decides depth ≤ l nor returns a circuit of depth ≤ l
--   - correction: the loop never tests depth 0 (U ∈ S_0 = {I}) → U = I is tested first and returns the empty circuit; reason: counterexample: G = {T, T†}, U = I, l = 2: the printed algorithm returns TT† of depth 2, not a circuit of minimal depth 0
--   - correction: running time O(|V_{n,G}|^{⌈l/2⌉} log(|V_{n,G}|^{⌈l/2⌉})) for every G and l → the bound when |V_{n,G}| ≥ 2 and l ≥ 1; clauses 1 and 2 hold for every G and l; reason: counterexample: n = 1, G = {X}, so V_{n,G} = {X} and N log N = 1 · log 1 = 0 while the algorithm performs ⌈l/2⌉ ≥ 1 iterations of positive cost; likewise l = 0 gives N = 1 and log N = 0 while the depth-0 test costs one step
--   - reading: U can be implemented by a circuit over G of depth at most l → ∃ m ≤ l, U ∈ S_m (a product of exactly m elements of V_{n,G}); reason: the literal p. 4 wording ("depth at most m if ... U_1U_2···U_m") would make depth-at-most non-monotone when I ∉ V_{n,G}; the reading is the one the algorithm's correctness paragraph uses ("the smallest depth less than or equal to l")
--   - reading: RAM model of computation (footnote 1) → one unit of cost per multiplication, adjoint or three-way comparison of unitaries and per list or array step, counted in the Timed monad; reason: the paper's bound has no dependence on n beyond |V_{n,G}|, so unitary-level operations are unit cost
--   - reading: O(·) → one absolute constant C, chosen before all other quantities; reason: the O-notation of an algorithm analysis is a constant independent of the input
--   - generalization: a strict lexicographic ordering on unitaries ("ordered according to the first element on which they differ") → every linear order on 2^n × 2^n complex matrices; reason: the paper's lexicographic order is one linear order, so the statement specializes to it
--   - encoding: S_i a set of unitaries; the output a circuit V W → S_i a list of (unitary, circuit) pairs, of length |V_{n,G}|^i, possibly with repeated unitaries; the output a list of layers (each a list of placed gates); reason: the paper's "circuit" is a specific sequence of gates (p. 4); repetitions do not change any membership test and keep |S_i| ≤ |V_{n,G}|^i
--   - encoding: the algorithm receives G and U, and uses V_{n,G} → the algorithm receives a duplicate-free list of (layer, unitary) pairs enumerating V_{n,G}, with every label a layer over G; reason: the pseudocode multiplies by V_{n,G} (S_i := V_{n,G}S_{i−1}) and returns circuits, so it needs V_{n,G} with one layer per element; the paper's bound counts no cost for producing it. For infinite V_{n,G} no enumeration exists and the paper's bound is meaningless
--   - encoding: G a fixed set of gates → G : Set Gate with no finiteness assumption; reason: finiteness of V_{n,G} is carried by the enumeration hypothesis; no instance changes
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, §2, p. 4 (main result, with footnote 1: RAM model), for MITM-factor, §3, p. 6, analysed on pp. 6–7

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_MITMSynthesis_depthOneSet
import Definitions.Def_MITMSynthesis_S
import Definitions.Def_MITMSynthesis_mitmFactor

namespace MITMSynthesis

/-- **Main result: depth-optimal synthesis in `O(|V_{n,G}|^{⌈l/2⌉} log |V_{n,G}|^{⌈l/2⌉})` time.**
Amy–Maslov–Mosca–Roetteler, arXiv:1206.0758v3, §2, p. 4 (with footnote 1, the RAM model), for the
algorithm MITM-factor of §3, p. 6 (corrected), analysed on pp. 6–7.

There is one absolute constant `C` such that for every number of qubits `n`, every instruction
set `G` (closed under inverses), every duplicate-free enumeration `vs` of `V_{n,G}` by layers,
every linear order `ord` on `2^n × 2^n` matrices, every unitary `U ∈ U(2^n)` and every depth bound
`l`, the run `mitmFactor vs U l`
(A) decides whether `U` is implementable over `G` in depth at most `l`;
(B) when it returns a circuit, the circuit is a list of layers over `G` implementing `U`
(`U₁ U₂ ⋯ U_m = U`) in minimal depth;
(Cost) if `|V_{n,G}| ≥ 2` and `l ≥ 1`, the number of unit-cost steps is at most
`C · N · log N` with `N = |V_{n,G}|^{⌈l/2⌉}`, `⌈l/2⌉ = (l + 1) / 2`. -/
theorem mitm_factor_main :
    ∃ C : ℝ, ∀ (n : ℕ) (G : Set Gate) (vs : List (List (Placement n) × Matrix (Q n) (Q n) ℂ))
      (ord : LinearOrder (Matrix (Q n) (Q n) ℂ)) (U : Matrix (Q n) (Q n) ℂ) (l : ℕ),
      IsInstructionSet G → IsLayerEnumeration G vs → U ∈ Matrix.unitaryGroup (Q n) ℂ →
      ((mitmFactor (ord := ord) vs U l).val.isSome ↔ ∃ m ≤ l, U ∈ S (depthOneSet n G) m) ∧
      (∀ c, (mitmFactor (ord := ord) vs U l).val = some c →
        (∀ L ∈ c, IsLayer G L) ∧ (c.map layerUnitary).prod = U ∧
          IsMinDepth (depthOneSet n G) U c.length) ∧
      (2 ≤ (depthOneSet n G).ncard → 1 ≤ l →
        ((mitmFactor (ord := ord) vs U l).cost : ℝ) ≤
          C * ((depthOneSet n G).ncard : ℝ) ^ ((l + 1) / 2) *
            Real.log (((depthOneSet n G).ncard : ℝ) ^ ((l + 1) / 2))) := by sorry

end MITMSynthesis
