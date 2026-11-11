-- Prove2me | Theorems.Thm_GPTIP632_Classical_lemma_E_2
-- name    : GPTIP632.Classical.lemma_E_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:26.280795+00:00
-- url     : https://prove2.me/theorems/34fc1f01-5bb9-4c43-902c-5d22ea7635fb
-- title:
--   Lemma E.2: every prover is matched by classical response distributions; $\mathrm{val}_{\mathcal G}$ is the sup over classical randomised provers
-- statement:
--   Let $\mathcal G$ satisfy the standing assumptions, let $V$ be an $r$-round verifier whose messages are classical registers, and let $x$ be an input.
--
--   1. For every prover strategy $P$ in $\mathcal G$ there are conditional distributions $\pi_i(a_i\mid q_1,a_1,\dots,q_{i-1},a_{i-1},q_i)$, $i=1,\dots,r$, such that for every record
--   $$\Pr[z,a]=\Pr_V[z\mid a]\prod_i\pi_i(a_i\mid q_{\le i},a_{<i}).$$
--   Thus $P$ produces the same distribution of records, hence the same acceptance probability, as the classical randomised prover with memory that answers according to $\pi_1,\dots,\pi_r$.
--   2. Conversely, every classical randomised prover is realised by a prover strategy in $\mathcal G$ with the same distribution of records.
--   3. Hence
--   $$\mathrm{val}_{\mathcal G}(V_x)=\sup\{\Pr[V_x\leftrightarrow P\text{ accepts}]:P\text{ a classical randomised prover}\}.$$
--
--   The lemma removes the theory from the prover's side: only the verifier's circuit remains to be evaluated.
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
--   - encoding: a classical randomised prover with memory answering according to π_1, …, π_r, and its acceptance probability → a family resp i h q a of conditional distributions on the answer strings of length |A_i|, with acceptance probability ∑ Pr_V[z | a] ∏_i π_i over the accepting records; reason: the acceptance probability of such a prover, by the first clause and the realisation clause
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, p.25 (PDF p.27), Lemma E.2

import Mathlib
import Definitions.Def_GPTIP632_Classical_ClassicalProver

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace GPTIP632.Classical

/-- **Lemma E.2 (Classical simulation of prover responses)**, p.25: for a verifier `V` with classical
messages, (1) every prover strategy `P` in `G` has conditional distributions `π_i` with
`Pr[z, a] = Pr_V[z | a] ∏_i π_i(a_i | q_{≤i}, a_{<i})` for every record; (2) conversely every
classical randomised prover is realised by a prover strategy in `G` with the same distribution of
records; (3) hence `val_G(V_x)` is the supremum of the acceptance probabilities of classical
randomised provers. -/
theorem lemma_E_2 (G : Theory) (hG : G.Standing) (V : VData G) (hV : V.IsVerifier)
    (hcl : V.ClassicalMessages) (x : Str) :
    (∀ P : Prover V x, ∃ resp, V.IsCRProver x resp ∧
      ∀ ws q a, V.prob x P ws q a = V.PrV x a ws q * V.crWeight x resp q a) ∧
    (∀ resp, V.IsCRProver x resp → ∃ P : Prover V x,
      ∀ ws q a, V.prob x P ws q a = V.PrV x a ws q * V.crWeight x resp q a) ∧
    V.val x = sSup {t | ∃ resp, V.IsCRProver x resp ∧ V.crAcc x resp = t} := by sorry

end GPTIP632.Classical
