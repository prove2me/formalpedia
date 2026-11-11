-- Prove2me | Theorems.Thm_GPTIP632_Classical_fact_E_4
-- name    : GPTIP632.Classical.fact_E_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:00.90919+00:00
-- url     : https://prove2.me/theorems/f035983a-0e31-4751-9e6e-a5cb55f2056b
-- title:
--   Fact E.4: deterministic provers suffice; $\mathrm{val}_{\mathcal G}(V_x)=F(\emptyset)$ by the sum–max recursion
-- statement:
--   Let $\mathcal G$ satisfy the standing assumptions, let $V$ be an $r$-round verifier with classical messages, and let $x$ be an input. For each complete transcript $(q,a)$ define the weight
--
--   $$
--   W(q,a)=\sum_{z\text{ records }q,\ \mathrm{acc}=1}\Pr_V[z\mid a],
--   $$
--
--   and define $F$ on partial transcripts by backward recursion: $F(q,a)=W(q,a)$; $F(h,q)=\max_aF(h,q,a)$ when the next move is an answer; $F(h)=\sum_qF(h,q)$ when the next move is a question, $q$ and $a$ ranging over the bit strings of the message lengths. Then
--
--   $$
--   \mathrm{val}_{\mathcal G}(V_x)=F(\emptyset)=\sum_{q_1}\max_{a_1}\cdots\sum_{q_r}\max_{a_r}W(q,a),
--   $$
--
--   and the value is attained by a deterministic prover $f=(f_1,\dots,f_r)$ with $a_i=f_i(q_1,\dots,q_i)$.
--
--   The sums run over the verifier's private records before the maxima, so the prover never sees them; this recursion is what the upper bound of Theorem 1.1 evaluates in polynomial space.
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
--   - encoding: F on partial transcripts by backward recursion; a deterministic prover a_i = f_i(q_1, …, q_i) → Frec k h with k rounds still to play after the transcript h, the questions and answers ranging over the bit strings of the message lengths; f i [q_1, …, q_i] a string of length |A_i|, used as the point-mass prover detResp f; reason: the same recursion, indexed by the number of remaining rounds
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, p.26 (PDF p.28), Fact E.4

import Mathlib
import Definitions.Def_GPTIP632_Classical_ClassicalProver

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace GPTIP632.Classical

/-- **Fact E.4 (Deterministic provers suffice)**, p.26: for a verifier `V` with classical messages,
`val_G(V_x) = F(∅)`, where `F(q, a) = W(q, a) = ∑_{z records q, acc = 1} Pr_V[z | a]` at complete
transcripts, `F(h, q) = max_a F(h, q, a)` and `F(h) = ∑_q F(h, q)`; and the value is attained by a
deterministic prover `a_i = f_i(q_1, …, q_i)`. -/
theorem fact_E_4 (G : Theory) (hG : G.Standing) (V : VData G) (hV : V.IsVerifier)
    (hcl : V.ClassicalMessages) (x : Str) :
    V.val x = V.Fempty x ∧
    ∃ f : ℕ → List (List Bool) → List Bool, (∀ i qs, (f i qs).length = (V.A x i).length) ∧
      V.crAcc x (VData.detResp f) = V.val x := by sorry

end GPTIP632.Classical
