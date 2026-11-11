-- Prove2me | Theorems.Thm_GPTIP632_Classical_fact_C_2
-- name    : GPTIP632.Classical.fact_C_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:05:53.762191+00:00
-- url     : https://prove2.me/theorems/90601e68-384f-49f3-9805-2d656073da66
-- title:
--   Fact C.2: record probabilities $\Pr[z\mid a]$ and their sums over polynomial-time decidable sets are approximable in polynomial space
-- statement:
--   Let $\mathcal G$ satisfy the standing assumptions, and consider the polynomial-time uniform family of adaptive circuits of a verifier $V$ with classical messages, run with a classical input $a$ (the answer strings) fed into its answer wires. Write $\Pr_V[z\mid a]$ for the probability of the record $z$ (eq. (2)).
--
--   1. For every polynomial $q$ there is a deterministic polynomial-space algorithm that, given $x$, a classical input $a$ and a record $z$, outputs a rational number $\tilde P$ with
--   $$|\tilde P-\Pr_V[z\mid a]|\le2^{-q(|x|)}.$$
--   2. The same holds for the sums $\sum_{z\in Z}\Pr_V[z\mid a]$ over any polynomial-time decidable set $Z$ of records. The set may depend on $x$, on $a$ and on an auxiliary string $w$ given to the algorithm, for example a target question string.
--
--   This is the path-sum method of Lee and Barrett: the gate entries are efficiently approximable, so the exponentially large matrix products can be summed term by term in polynomial space.
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
--   - encoding: a polynomial-time uniform family {C_x} in G with classical input a → the adaptive circuit of a classical-message verifier with the answers a fixed on its answer wires (Pr_V[z | a]); reason: a family with classical input a is the one-round verifier with an empty question, a first stage that halts at once and the input wires as its answer; this is the family used in Theorem E.6
--   - generalization: a record z of length poly(|x|); a polynomial-time decidable set Z of records → the algorithm is correct on every input, with space polynomial in the input length; Z may depend on x, a and an auxiliary string w given to the algorithm; reason: inputs of length poly(|x|) give space poly(|x|); a set of records not depending on a, w is the special case
--   - encoding: a deterministic polynomial-space algorithm that outputs a rational number → an OTM run with the empty oracle that halts on every input after visiting at most s(|input|) cells, with the encoding encRat of a rational on its work tape (sign bit, |numerator| and denominator in binary); reason: a fixed self-delimiting rational encoding
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, p.21 (PDF p.23), Fact C.2 and eqs. (2)–(3)

import Mathlib
import Definitions.Def_GPTIP632_Classical_ClassicalProver

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace GPTIP632.Classical

open _root_.Classical in
/-- **Fact C.2 (Path-sum representation)**, p.21, for the verifier's polynomial-time uniform family
of adaptive circuits with the classical input `a` supplied on its answer wires: for every
polynomial `q` a deterministic polynomial-space algorithm, given `x`, `a` and a record `z`, outputs a
rational within `2^{-q(|x|)}` of `Pr_V[z | a]`; and the same for the sums `∑_{z ∈ Z} Pr_V[z | a]` over
any polynomial-time decidable set `Z` of records (which may depend on `x`, `a` and an auxiliary
string `w` given to the algorithm). -/
theorem fact_C_2 (G : Theory) (hG : G.Standing) (V : VData G) (hV : V.IsVerifier)
    (hcl : V.ClassicalMessages) :
    (∀ qp : Polynomial ℕ,
      PolySpaceApprox
        (fun y : Str × (ℕ → List ℕ) × (ℕ → List Bool) × (ℕ → List Bool) =>
          V.encRecord y.1 y.2.1 y.2.2.1 y.2.2.2)
        (fun y => V.PrV y.1 y.2.2.2 y.2.1 y.2.2.1)
        (fun y => 1 / 2 ^ qp.eval y.1.length)) ∧
    (∀ Z : Str → (ℕ → List Bool) → Str → (ℕ → List ℕ) → (ℕ → List Bool) → Prop,
      PolyTimeDecidable
        (fun y : (Str × (ℕ → List Bool) × Str) × (ℕ → List ℕ) × (ℕ → List Bool) =>
          tup [V.encRecord y.1.1 y.2.1 y.2.2 y.1.2.1, y.1.2.2])
        (fun y => Z y.1.1 y.1.2.1 y.1.2.2 y.2.1 y.2.2) →
      ∀ qp : Polynomial ℕ,
        PolySpaceApprox
          (fun y : Str × (ℕ → List Bool) × Str => tup [V.encRecord y.1 (fun _ => []) (fun _ => []) y.2.1, y.2.2])
          (fun y => V.recordSumWQ y.1 fun ws q =>
            if Z y.1 y.2.1 y.2.2 ws q then V.PrV y.1 y.2.1 ws q else 0)
          (fun y => 1 / 2 ^ qp.eval y.1.length)) := by sorry

end GPTIP632.Classical
