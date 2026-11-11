-- Prove2me | Theorems.Thm_GPTIP632_Classical_theorem_E_5
-- name    : GPTIP632.Classical.theorem_E_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:04:22.43442+00:00
-- url     : https://prove2.me/theorems/58050353-ba34-4c4a-902e-6001eb17346c
-- title:
--   Theorem E.5: $\mathsf{PSPACE}\subseteq\mathsf{GIP}_{\mathrm{cl}}(\mathcal G)\subseteq\mathsf{GIP}(\mathcal G)$, also for the public-coin subclass
-- statement:
--   For every theory $\mathcal G$ satisfying the standing assumptions (T1)–(T4),
--
--   $$
--   \mathsf{PSPACE}\subseteq\mathsf{GIP}_{\mathrm{cl}}(\mathcal G)\subseteq\mathsf{GIP}(\mathcal G).
--   $$
--
--   The same holds with the public-coin subclass of $\mathsf{GIP}_{\mathrm{cl}}(\mathcal G)$ — the protocols in which every question $Q_i$ is a string of fresh fair-coin outcomes, sent to the prover unchanged — in place of $\mathsf{GIP}_{\mathrm{cl}}(\mathcal G)$. All classes are classes of promise problems, with completeness $2/3$ and soundness $1/3$.
--
--   This is the lower half of Theorem 1.1: no theory satisfying the standing assumptions loses the power of classical interactive proofs, whatever provers it allows.
--
--   Differences from the source:
--   - encoding: a system is (V_A, V_A^+, u_A) with V_A a finite-dimensional real vector space → a system has a finite coordinate type ι with V_A = ι → ℝ, the cone a subset, and the unit a coordinate vector paired by the dot product; reason: every finite-dimensional space is ℝ^ι in a basis; (T4) refers to these fixed coordinates
--   - encoding: the standard classical systems Δ_n (n ≥ 1) → the designated system cl n is Δ_{n+1}, with coordinates Fin (n+1); cl 0 = Δ_1 is the trivial system I; reason: an index shift; Δ_1 has V = ℝ, V⁺ = ℝ≥0, u = id, which is I
--   - generalization: allowed operations are closed under sequential and parallel composition → closure is required for channel∘channel and instrument∘instrument (product outcome set) and for parallel composition of channels and of instruments; compositions mixing a channel with an instrument are not required; reason: fewer requirements on the theory, so more theories qualify; every theory of Definition B.16 satisfies these conditions, so the statement specializes to the source
--   - reading: (T3) every stochastic map between classical systems is an allowed channel → every column-stochastic matrix between systems obtained from the designated Δ_n by forming composites (IsStdClassical), in their own coordinates, is an allowed channel; reason: p.16: for classical A and B the composite is Δ_nm; 'classical' means the effective encodings of (T3), not every simplex (p.23)
--   - encoding: (T3) the readout effects of Δ_n are allowed → the readout measurement of Δ_n, with effects the coordinate functionals, is an allowed instrument to the trivial system; reason: a measurement is an instrument with trivial output (Definition B.11)
--   - reading: (T4) the gate set contains the preparation of a fixed state of each elementary system, the elementary discards, the readout of classical bits, the preparation of a fair coin, and a universal set of classical reversible gates [Tof80] → the classical bit Δ_2 is an elementary system a, and the gate set contains, besides a fixed preparation and the discard of every elementary system, the readout of a, the fair coin on a, the preparation of δ_0 on a, NOT and Toffoli on a; reason: Toffoli universality needs constant bits; with fair coins only, reversible gates never produce a known bit, and the proof of Lemma E.1 (p.24) copies classical registers with reversible gates
--   - encoding: a (deterministic) polynomial-time Turing machine → a deterministic oracle Turing machine (QAdvFew.PoQOracle.OTM) run with the empty oracle for p(|input|) steps, its output read off the work tape; reason: a clocked machine is a polynomial-time machine and conversely
--   - encoding: the uniformity machine names the next gate and the wires it acts on → wires are named by their positions in the register; the named wires are removed and the gate's output wires are appended at the end; reason: a placement convention; positions are tracked by the polynomial-time machine
--   - encoding: the uniformity machine is given x and the outcomes recorded so far → it is given x, the stage index i (in unary) and the outcomes recorded so far; reason: stage boundaries are not recorded outcomes; the index is computable from the run in polynomial time
--   - reading: the message types are fixed by x (with padding) → the message types of round i are output by a polynomial-time machine on (x, i); reason: Definition D.1: the gates and wires are determined by x and the recorded outcomes via the uniformity machine
--   - encoding: an adaptive circuit is a deterministic procedure that names the next gate and its wires or halts; at most p(|x|) gate applications and wires → the machine must name a valid gate application, stay within p(|x|) gate applications and p(|x|) wires, and end each stage with the declared message wires, on every syntactically supplied record (WellFormed), including zero-probability and wrong-length message records; reason: a total completion of the circuit procedure; off-domain histories can be completed by ignoring malformed labels and using fixed preparations for the declared outgoing wires, without changing any physical record
--   - encoding: in stage r+1 the verifier produces a classical bit acc among its recorded outcomes → the verifier accepts iff the last outcome recorded in stage r+1 is 1; reason: an adaptive circuit can record its decision last
--   - encoding: the verifier may read out each classical message before sending it and on receipt (pp.24–25); this refines its record → messages whose wires are all classical bits are read out when exchanged; the question and answer strings are recorded and seen by the uniformity machine; reason: reading a classical register does not disturb it (Fact B.10), changes no acceptance probability, and is realised by the verifier's gates (p.24); the paper assumes this normal form in §E.1
--   - encoding: the verifier's record z, including the questions q_1, …, q_r and acc → the gate outcomes of each stage ws : ℕ → List ℕ together with the recorded question and answer strings q, a : ℕ → List Bool; reason: the same information, split by stage
--   - encoding: val_G(V_x) = sup_P Pr[V_x ↔ P accepts] → sSup in ℝ of the set of acceptance probabilities of all prover strategies; reason: the set is nonempty and bounded by 1 for a verifier of a theory, so sSup is the supremum
--   - encoding: PSPACE, as a class of promise problems → KTUnitary.Synth.PromisePSPACE at the empty oracle: an OTM halting on every input within space p(|x|) (input cells counted) and answering correctly on L_yes ∪ L_no; reason: the standard machine definition; counting the input cells changes nothing for polynomial space
--   - encoding: public coin: every question Q_i is a string of fresh fair-coin outcomes, sent to the prover unchanged → a fair-coin gate g on a classical bit wire a exists, every Q_i consists of wires a, and in every stage i < r the last |Q_i| gate applications before the halt are g (started from any record of the earlier rounds); reason: fresh outputs of the coin gate that no gate touches afterwards; the verifier knows them through the recorded readout
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, p.26 (PDF p.28), Theorem E.5 and the definition of public coin on p.26

import Mathlib
import Definitions.Def_GPTIP632_Classical_Protocol
import Definitions.Def_KTUnitary_Synth_PromisePSPACE

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace GPTIP632.Classical

/-- **Theorem E.5 (Polynomial-space lower bound)**, p.26: for every theory `G` (satisfying the
standing assumptions), `PSPACE ⊆ GIP_cl(G) ⊆ GIP(G)`, and the same with the public-coin subclass of
`GIP_cl(G)` in place of `GIP_cl(G)`. -/
theorem theorem_E_5 (G : Theory) (hG : G.Standing) :
    KTUnitary.Synth.PromisePSPACE O₀ ⊆ GIPcl G ∧ GIPcl G ⊆ GIP G ∧
    KTUnitary.Synth.PromisePSPACE O₀ ⊆ GIPclPublicCoin G ∧ GIPclPublicCoin G ⊆ GIP G := by sorry

end GPTIP632.Classical
