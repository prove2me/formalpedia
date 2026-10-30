-- Prove2me | Theorems.Thm_MITMSynthesis_mitm_factor_correct
-- name    : MITMSynthesis.mitm_factor_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:07:52.642994+00:00
-- url     : https://prove2.me/theorems/8cd27d79-9d95-4905-9f51-87c2d7cae8e4
-- title:
--   Correctness of MITM-factor: decision and minimal-depth synthesis (corrected: no depth-(l+1) test, depth-0 test added)
-- statement:
--   Let $\mathcal G$ be an instruction set, $n \in \mathbb N$, $V_{n,\mathcal G}$ the set of depth-one unitaries over $\mathcal G$ and $S_m$ the set of unitaries implementable in depth $m$. Let `vs` be a duplicate-free list of (layer, unitary) pairs enumerating $V_{n,\mathcal G}$, fix any linear order on $2^n\times2^n$ matrices, a unitary $U \in U(2^n)$ and $l \in \mathbb N$. Run MITM-factor (with depth $0$ tested first and depth $2i$ tested only when $2i \le l$). Then:
--
--   1. **(decision)** it returns a circuit if and only if $U$ can be implemented in depth at most $l$:
--   $$
--   \text{MITM-factor returns a circuit} \iff \exists\, m \le l,\ U \in S_m ;
--   $$
--   2. **(minimal-depth synthesis)** if it returns a circuit $L_1, \dots, L_k$, then every $L_j$ is a layer over $\mathcal G$, their unitaries satisfy $U_1 U_2 \cdots U_k = U$, and $k$ is the minimal depth of $U$: $U \in S_k$ and $k \le m$ whenever $U \in S_m$.
--
--   This is the correctness half of the paper's main result: the algorithm stops at the smallest depth not exceeding $l$ at which $U$ is implementable and returns a circuit of that depth.
--
--   Differences from the source:
--   - correction: the loop tests S_i†U ∩ S_i ≠ ∅ (depth 2i) in every iteration i ≤ ⌈l/2⌉, so for odd l it tests depth l+1 → depth 2i is tested only when 2i ≤ l; reason: counterexample: n = 1, G = {T, T†}, V_{n,G} = {T, T†}, U = P = T², l = 1: the printed algorithm returns the circuit TT of depth 2 > l although P ∉ S_0 ∪ S_1, so it neither decides depth ≤ l nor returns a circuit of depth ≤ l
--   - correction: the loop never tests depth 0 (U ∈ S_0 = {I}) → U = I is tested first and returns the empty circuit; reason: counterexample: G = {T, T†}, U = I, l = 2: the printed algorithm returns TT† of depth 2, not a circuit of minimal depth 0
--   - reading: U can be implemented by a circuit over G of depth at most l → ∃ m ≤ l, U ∈ S_m (a product of exactly m elements of V_{n,G}); reason: the literal p. 4 wording ("depth at most m if ... U_1U_2···U_m") would make depth-at-most non-monotone when I ∉ V_{n,G}; the reading is the one the algorithm's correctness paragraph uses ("the smallest depth less than or equal to l")
--   - generalization: a strict lexicographic ordering on unitaries ("ordered according to the first element on which they differ") → every linear order on 2^n × 2^n complex matrices; reason: the paper's lexicographic order is one linear order, so the statement specializes to it
--   - encoding: S_i a set of unitaries; the output a circuit V W → S_i a list of (unitary, circuit) pairs, of length |V_{n,G}|^i, possibly with repeated unitaries; the output a list of layers (each a list of placed gates); reason: the paper's "circuit" is a specific sequence of gates (p. 4); repetitions do not change any membership test and keep |S_i| ≤ |V_{n,G}|^i
--   - encoding: the algorithm receives G and U, and uses V_{n,G} → the algorithm receives a duplicate-free list of (layer, unitary) pairs enumerating V_{n,G}, with every label a layer over G; reason: the pseudocode multiplies by V_{n,G} (S_i := V_{n,G}S_{i−1}) and returns circuits, so it needs V_{n,G} with one layer per element; the paper's bound counts no cost for producing it. For infinite V_{n,G} no enumeration exists and the paper's bound is meaningless
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, §3, p. 6 (paragraph after MITM-factor: "so the algorithm terminates at the smallest depth less than or equal to l ... returns one such circuit of minimal depth")

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_MITMSynthesis_depthOneSet
import Definitions.Def_MITMSynthesis_S
import Definitions.Def_MITMSynthesis_mitmFactor

namespace MITMSynthesis

/-- **Correctness of MITM-factor (corrected).** Amy–Maslov–Mosca–Roetteler, arXiv:1206.0758v3, §3,
p. 6: "the algorithm terminates at the smallest depth less than or equal to l for which there
exists a circuit implementing U. In the case where U can be implemented in depth at most l, the
algorithm returns one such circuit of minimal depth."

Let `G` be an instruction set, `vs` a duplicate-free enumeration of `V_{n,G}` by layers, `ord`
any linear order on `2^n × 2^n` matrices, `U` unitary and `l ∈ ℕ`. For the corrected algorithm
`mitmFactor` (depth 0 tested first; depth `2i` tested only when `2i ≤ l`):
(A) it returns a circuit iff `U` is implementable in some depth `m ≤ l`;
(B) a returned circuit consists of layers over `G`, its unitaries multiply (`U₁ U₂ ⋯ U_m`) to `U`,
and its length is the minimal depth of `U` over `G`. -/
theorem mitm_factor_correct {n : ℕ} {G : Set Gate} (hG : IsInstructionSet G)
    (vs : List (List (Placement n) × Matrix (Q n) (Q n) ℂ)) (hvs : IsLayerEnumeration G vs)
    (ord : LinearOrder (Matrix (Q n) (Q n) ℂ))
    (U : Matrix (Q n) (Q n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Q n) ℂ) (l : ℕ) :
    ((mitmFactor (ord := ord) vs U l).val.isSome ↔ ∃ m ≤ l, U ∈ S (depthOneSet n G) m) ∧
    (∀ c, (mitmFactor (ord := ord) vs U l).val = some c →
      (∀ L ∈ c, IsLayer G L) ∧ (c.map layerUnitary).prod = U ∧
        IsMinDepth (depthOneSet n G) U c.length) := by sorry

end MITMSynthesis
