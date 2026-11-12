-- Prove2me | Theorems.Thm_FourWayStream_ARHM_cut_gives_message
-- name    : FourWayStream.ARHM.cut_gives_message
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:48:33.101718+00:00
-- url     : https://prove2.me/theorems/371c73cb-7f31-4f44-bbbe-61c14da85b12
-- title:
--   Lemma 5.9 — a cut gives a message
-- statement:
--   **Lemma 5.9 (A cut gives a message).** Fix a streaming algorithm for $\mathrm{ARHM}_{N,m}$ with $L$ copies and a cut followed by $s$ requests (Definition 5.8): the stream up to the cut is determined by the input $X$, public randomness $r$ and private randomness, and the $s$ items after the cut are requests whose tags are determined by $r$ and whose factor indices are independent of $X$ and of the prefix. If the algorithm has at most $q$ qubits of live memory, classical bits included, then there is a one-way protocol without prior entanglement, using the same public coins, in which Alice, given $X$, sends $q$ qubits ($q$ bits, that is one of at most $2^q$ symbols, if the algorithm is classical), and Bob, given the $s$ factor indices one at a time, answers each before seeing the next, such that for every value of the coins, of $X$ and of the indices
--   $$P_{\text{protocol}}[\text{Bob answers } o_1,\dots,o_s]=P_{\text{algorithm}}[\text{the answers to the } s \text{ requests after the cut are } o_1,\dots,o_s].$$
--   For algorithms whose steps depend on the stage, the position of the cut must be determined by the public randomness.
--
--   This is the bridge from streaming to one-way communication used by both lower bounds.
--
--   Differences from the source:
--   - reading: §4.2: a classical controller applies, for every item, a circuit from a fixed finite set of gates and measurement operators to an array of qubits → every item is processed by an arbitrary quantum instrument (finite complete Kraus family indexed by the output) on the memory C^d; the finite gate set is not modelled; reason: §4.2 is ambiguous: it states that the lower bounds hold for arbitrary channels, and the paper's own algorithm (Prop 5.7) uses exact phases e^{iπ/µ} and exact Fourier and matching-basis measurements, which are not circuits over a fixed finite gate set
--   - generalization: algorithms of the §4.2 model, in which the stage enters only through memory → also algorithms whose instruments or transitions depend on the stage, provided the cut position is determined by the public randomness (for stage-independent algorithms the position may depend on X and private randomness, as in Definition 5.8); reason: a larger class; for the paper's algorithms (stage independent) the cut is as general as Definition 5.8
--   - reading: Bob continues the algorithm on "his s requests" → the tags of the s requests after the cut are determined by the public randomness; their factor indices are Bob's inputs; reason: Bob must know the request items to continue the algorithm; in both uses (Prop 5.12, Cor 5.15) the tags are fixed or generated from public randomness, as the proof of Prop 5.12 states
--   - encoding: jointly with X and the indices, Bob's answers have the same distribution as the algorithm's → equality of the conditional answer laws for every value of the coins, of X and of the indices, with the protocol's coin distribution equal to the cut's; reason: pointwise equality gives equality of the joint law for every distribution of X and independent indices
--   - encoding: [N], [L], [m], [N − 1], edges {u, v}, bits in {0,1} → Fin N, Fin L, Fin m, Fin (N − 1) (0-based), Sym2 (Fin N), Bool with xor; reason: relabelling; no instance changes
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §5.2, p.22, Lemma 5.9 (Definition 5.8, p.22)

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream
import Definitions.Def_FourWayStream_ARHM_Protocols

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM

/-- Lemma 5.9 (A cut gives a message), p.22. For a cut followed by `s` requests (Definition 5.8):
if the algorithm has at most `q` qubits of live memory (classical bits included), there is a one-way
protocol without prior entanglement, with the same public coins, in which Alice, given `X`, sends `q`
qubits (`q` bits, i.e. at most `2^q` symbols, if the algorithm is classical) and Bob, given the `s`
factor indices one at a time, answers each before seeing the next, such that for every value of the
coins, of `X` and of the indices, Bob's answers have the same distribution as the algorithm's answers
to the `s` requests after the cut. The cut position may depend on `X` and private randomness when the
algorithm's steps do not depend on the stage (the paper's model); for stage-dependent algorithms the
position must be determined by the public randomness. -/
theorem cut_gives_message (N m L s : ℕ) (C : Cut N m L s) (hC : C.Valid) :
    (∀ (A : QStreamAlg N m L) (q : ℕ), A.Valid → A.space ≤ q →
        (A.StageIndependent ∨ C.PositionPublic) →
      ∃ P : QSeqProtocol N s (Fin (N - 1)) C.nR, P.Valid ∧ P.coin = C.pub ∧ P.d ≤ 2 ^ q ∧
        ∀ r x ks o, P.outProb r x ks o = C.qSuffixLaw A r x ks o) ∧
    (∀ (A : CStreamAlg N m L) (q : ℕ), A.Valid → A.space ≤ q →
        (A.StageIndependent ∨ C.PositionPublic) →
      ∃ P : CSeqProtocol N s (Fin (N - 1)) C.nR, P.Valid ∧ P.coin = C.pub ∧ P.M ≤ 2 ^ q ∧
        ∀ r x ks o, P.outProb r x ks o = C.cSuffixLaw A r x ks o) := by sorry

end FourWayStream.ARHM
