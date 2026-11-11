-- Prove2me | Theorems.Thm_GPTIP632_Classical_lemma_E_1
-- name    : GPTIP632.Classical.lemma_E_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:13.788355+00:00
-- url     : https://prove2.me/theorems/b2f9cc57-df87-4158-bdff-073d957c18a6
-- title:
--   Lemma E.1: product form of the joint state; $\Pr[z,a]=\Pr_V[z\mid a]\,\pi(a\mid q)$
-- statement:
--   Let $\mathcal G$ satisfy the standing assumptions, let $V$ be an $r$-round verifier whose messages are classical registers, $x$ an input, and $P$ a prover strategy with initial state $\tau_0$ and channels $\Pi_i$, decomposed as $\Pi_i(\delta_q\otimes\tau)=\sum_a\delta_a\otimes\Pi_i^{qa}(\tau)$ (eq. (5)). The verifier reads each question before sending it and each answer on receipt. For every record $(z,a)$ — the verifier's gate outcomes and recorded questions $q=(q_1,\dots,q_r)$, together with the answers $a=(a_1,\dots,a_r)$ — the unnormalised joint state of the verifier's register and the prover's system at the end of round $i$, conditioned on the record so far, is a product
--
--   $$
--   \sigma_i(z,a)\otimes\tau_i(q_1,a_1,\dots,q_i,a_i),\qquad\tau_i=\Pi_i^{q_ia_i}\circ\cdots\circ\Pi_1^{q_1a_1}(\tau_0),
--   $$
--
--   where $\sigma_i$ is the verifier's state in its own circuit with the answers fixed on the wires $A_i$. Consequently
--
--   $$
--   \Pr[z,a]=\Pr_V[z\mid a]\cdot\pi(a\mid q),\qquad\pi(a\mid q):=u\big(\tau_r(q_1,a_1,\dots,q_r,a_r)\big).\qquad(6)
--   $$
--
--   Classical messages thus decouple the parties: whatever systems the prover holds, only the classical numbers $\pi(a\mid q)$ reach the verifier.
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
--   - encoding: the joint state at the end of round i, conditioned on the record so far, is σ_i(z,a) ⊗ τ_i → for every i ≤ r(|x|), the joint vector at the start of stage i+1 equals σ_i(k) τ_i(p) at every coordinate (k, p) of the register and the prover's system, where σ_i is the verifier's state with the answers fixed (the same run outcome, budget and register); reason: the product form stated coordinatewise
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, p.25 (PDF p.27), Lemma E.1 and eq. (5)

import Mathlib
import Definitions.Def_GPTIP632_Classical_ClassicalProver

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace GPTIP632.Classical

/-- **Lemma E.1 (Product form)**, p.25: for a verifier `V` with classical messages and a prover
strategy `P`, along every record `(ws, q, a)` (gate outcomes, recorded questions, recorded answers)
the joint state of the verifier's register and the prover's system at the end of round `i` is the
product `σ_i ⊗ τ_i(q_1, a_1, …, q_i, a_i)`, where `σ_i` is the verifier's state with the answers fixed
on its wires and `τ_i = Π_i^{q_i a_i} ∘ ⋯ ∘ Π_1^{q_1 a_1}(τ_0)`. Consequently
`Pr[z, a] = Pr_V[z | a] · π(a | q)` with `π(a | q) = u(τ_r)` (eq. (6)). -/
theorem lemma_E_1 (G : Theory) (hG : G.Standing) (V : VData G) (hV : V.IsVerifier)
    (hcl : V.ClassicalMessages) (x : Str) (P : Prover V x) (ws : ℕ → List ℕ) (q a : ℕ → List Bool) :
    (∀ i, i ≤ V.R x →
      ProductForm (V.jointPre x P ws q a i) (V.verPre x ws q a i) (V.tauVec x P q a i)) ∧
    V.prob x P ws q a = V.PrV x a ws q * V.proverWeight x P q a := by sorry

end GPTIP632.Classical
