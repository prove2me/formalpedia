-- Prove2me | Theorems.Thm_LocalSweepFT_theorem_6_3
-- name    : LocalSweepFT.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:46:19.021818+00:00
-- url     : https://prove2.me/theorems/8f8e0439-4021-4ba4-83e6-50c649888ff8
-- title:
--   Theorem 6.3 (operator-requested pinned-down version) — 4D-Toric-encoded simulation with fixed sweep-rule correction failing w.p. $\le A(w\mu n)^k p^{cn}$
-- statement:
--   **Operator-requested pinned-down version.** The model, which the paper leaves partly informal, is pinned down as listed under the differences below; the theorem is otherwise at full strength.
--
--   There are constants $p_0\in(0,1)$, $A,c,K_1,K_2>0$ and $k\in\mathbb N$ with the following property. Let $n\ge1$ and let $\mathrm{rule}_1,\mathrm{rule}_2$ be sweep rules for the two sectors of the side-$n$ 4D Toric code (the $(4,2)$-Toric code). There is a referee $D$ for its nice encoding such that for every quantum circuit $C$ over $\{X,Z,CX,H,S,T\}$ and measurements, of depth $\mu\ge1$ and width $w\ge1$, there are a Toric encoded circuit $\tilde C$ whose registers are side-$n$ 4D Toric codes and an injective map $\mathrm{out}$ from the qubits of $C$ to the registers of $\tilde C$ with
--   1. $K_1\mu n\le\operatorname{depth}\tilde C\le K_2\mu n$ and $K_1(w+w\mu)n^8\le\operatorname{width}\tilde C\le K_2(w+w\mu)n^8$;
--   2. decoding the noiseless run of $\tilde C$ gives exactly $C(|0^w\rangle\langle0^w|)$;
--   3. for every $p\in(0,p_0)$ and every local stochastic Pauli noise of rate $p$,
--   $$\Pr\big[\text{decoded }\tilde C[E]\ne C(|0^w\rangle\langle0^w|)\big]\le A\,(w\mu n)^k\,p^{cn};$$
--   4. if $C$ is the identity circuit, every logical layer of $\tilde C$ is empty and every correction layer is the bare sweep cycle.
--
--   This is the main theorem of the paper: fault tolerance with a fixed, constant-depth, time-independent local correction cycle on a code without expansion, failure probability exponentially small in the code side $n$.
--
--   Differences from the source:
--   - reading: initialization stage of depth Θ(poly(log n)), "subjected to local stochastic noise", neither proved nor described (p.60) → registers start at t = 0 in exact encoded |0̄⟩, |H⟩, |S⟩, |T⟩ (Def 5.13 item 1) and the first fault layer precedes the first layer; reason: this is the paper's own interface: Lemma 6.2 is stated "after the initialization stage, namely when assuming the given input is encoded" (p.57); the black-box stage has no model in the paper
--   - encoding: Toric encoded circuit (Def 5.13) with gadgets and classical processing described informally (§§4.5–4.6) → hybrid circuit of R registers and nb reliable classical bits; logical layers of logical Paulis, classically controlled logical Paulis and CX, transversal CX, Z- and X-basis measurement into bits, two-bit classical gates; sweep layers of the sweep cycle on every register plus classical gates; depth counts every layer, classical ones included, and width counts every wire (R·C(d,d′)·n^d register qubits plus the nb classical bits); reason: p.4 ("reliable classical bits and logic"), Def 5.13 item 2, Remark 3.9 (conditional gates) and Fig. 11 (conditional use of |S⟩); the printed width (w + 2wµ)n^{2d} (p.57) includes the teleportation overhead of §4.6
--   - reading: C̃[E] with fault layers between layers (Def 3.4), N_E local stochastic: Pr[S ⊆ Loc(E)] ≤ p^{|S|}, faults Pauli (Def 3.7) → a single-qubit Pauli fault at every (layer, register qubit) location, applied before every layer (m = 1); ν any distribution on fault patterns with Pr[every location of S carries a non-identity Pauli] ≤ p^{|S|}; classical bits never faulty; reason: pp.4, 13–14; m = 1 is the most frequent noise Def 3.4 allows, and Loc(E) = the non-identity locations is the weakest hypothesis on N_E
--   - reading: simulation (Def 6.1): a referee D and a map from qubits to registers; (1) decoded noiseless run equals the states of C; (2) Pr[some register introduces a logical error w.r.t. D] < δ → D a quantum channel from one register to one qubit with D(Enc ρ Enc†) = ρ; decoding traces out all other wires and applies D to each register out j; failure is the event decoded C̃[E] ≠ C(|0^w⟩⟨0^w|); reason: the proof bounds exactly this event (p.58: "if D ∘ C̃[E] ≠ C̃ …"); the logical-error event of Def 6.1 is phrased for Pauli propagations of Clifford circuits and implies it
--   - encoding: measurements of C (Def 3.1) → dephasing channels in the measured basis, outcome kept in the qubit; reason: C has only qubit wires, so its output is a w-qubit state
--   - reading: a sweep rule flips "such an assignment" (Def 4.6), which one unspecified; "a fixed local rule" (p.5) → every pair of sweep rules (one per sector): local rules returning an admissible rooted chain whenever one exists and 0 otherwise; reason: the proofs of Claims 4.26–4.28 use only admissibility, and the algorithm after Claim 4.7 (p.20) is one such rule; the ∀ reading is the stronger one
--   - encoding: S′ ⊂ S of size d′ "fixed in advance" (Def 4.36) → S′ = {1_1, …, 1_{d′}}; reason: all choices are equivalent under the coordinate-permuting symmetry of the torus
--   - encoding: referee D: L(H^{⊗N}) → L(H^{⊗N}) (Def 6.1) → a channel in Choi–Kraus form (WildeQIT.QChannel, trace preserving) from one register to one qubit; reason: a referee is applied register by register (Def 6.1 (1)); the output qubits carry the logical state
--   - reading: ∃ p₀ ∀ N_E ∀ C ∃ C̃ simulating C with probability 1 − O(poly(w, µ, n)) p^{Ω(n)} → ∃ p₀ A c K₁ K₂ k, ∀ n ≥ 1, ∀ sweep rules, ∃ D, ∀ w µ ≥ 1, ∀ C, ∃ C̃ out, ∀ p < p₀, ∀ ν, Pr[fail] ≤ A·(wµn)^k·p^{cn}; reason: C̃, D and out do not depend on the noise in the construction (p.57), so choosing them first is stronger; D is a referee for the code (Def 6.1); every n ≥ 1 is equivalent to n large, since for small n Pr[fail] ≤ #locations·p is absorbed by a smaller c
--   - reading: depth Θ(µn + Polylog(n)) and width Θ((w + wµ)n^8) → K₁µn ≤ depth ≤ K₂µn and K₁(w + wµ)n^8 ≤ width ≤ K₂(w + wµ)n^8; reason: the polylog term is the initialization stage, outside the model (first difference); Θ(µn + polylog n) = Θ(µn) for µ ≥ 1; both sides kept as printed
--   - encoding: clause 2: a correction cycle takes O(1) depth and its gates do not depend on time; for the identity circuit the layers after initialization are the same → the sweep cycle is one layer with the same channel at every time (by the definition of the model); kept as a conjunct: if C has no gates, every logical layer of C̃ is empty and every sweep layer has no classical gates; reason: Def 5.13 ("the layers … at even times are sweep-cycles")
--   - encoding: "the n-length 4D Toric code" → the side-n (4, 2)-Toric code (d = 4, d′ = 2); reason: the 4D Toric code of the paper is the (d, d′) = (4, 2) case (p.4, p.6)
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Theorem 6.3, p.60

import Mathlib
import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_LocalSweepFT_xLog
import Definitions.Def_LocalSweepFT_IsSweepRule
import Definitions.Def_LocalSweepFT_encMat
import Definitions.Def_LocalSweepFT_IdealCircuit
import Definitions.Def_LocalSweepFT_ToricEncodedCircuit
import Definitions.Def_LocalSweepFT_failProb

namespace LocalSweepFT

/-- Theorem 6.3, p.60 (Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…)), operator-requested pinned-down version. There are
constants `p₀ ∈ (0, 1)`, `A, c, K₁, K₂ > 0` and `k` such that for every side length `n ≥ 1` and every
pair of sweep rules there is a referee `D` for the nice encoding of the side-`n` 4D (`(4, 2)`) Toric
code, and for every circuit `C` of depth `µ ≥ 1` and width `w ≥ 1` there is a Toric encoded circuit
`C̃` of side-`n` `(4, 2)`-Toric registers and an injective map `out` from the qubits of `C` to its
registers with
1. depth `Θ(µn)` and width `Θ((w + wµ)n⁸)` (both bounds, with `K₁`, `K₂`);
2. noiseless run decoding to `C(|0^w⟩⟨0^w|)`;
3. failure probability at most `A·(wµn)^k·p^{cn}` under every local stochastic Pauli noise of rate
   `p < p₀`;
4. if `C` is the identity circuit, every logical layer of `C̃` is empty and every correction layer is
   the bare sweep cycle.

**Formalization Note.** Pinned-down model: initialization by encoded `|0̄⟩, |H⟩, |S⟩, |T⟩` at
`t = 0`, followed by the first fault layer (the black-box initialization stage of p.60);
hybrid layers with reliable classical bits; a Pauli fault layer before every layer (`m = 1`);
exact-equality failure event; constants before `n`; `C̃`, `D`, `out` before the noise; every pair of
sweep rules; `Θ(µn + Polylog n) = Θ(µn)`; `S′ = {1_1, 1_2}`. -/
theorem theorem_6_3 :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ < 1 ∧ ∃ A c K₁ K₂ : ℝ, 0 < A ∧ 0 < c ∧ 0 < K₁ ∧ 0 < K₂ ∧ ∃ k : ℕ,
      ∀ (n : ℕ) [NeZero n] (rule₁ : LocalRule 4 2) (rule₂ : LocalRule 4 (4 - 2)),
        IsSweepRule (ZMod n) rule₁ → IsSweepRule (ZMod n) rule₂ →
        ∃ D : WildeQIT.QChannel (QCell 4 2 n → ZMod 2) (Fin 1 → ZMod 2),
          IsReferee (Sfix (by norm_num : 2 ≤ 4)) D ∧
          ∀ (w μ : ℕ), 1 ≤ w → 1 ≤ μ → ∀ C : IdealCircuit w μ,
            ∃ (Ct : ToricEncodedCircuit 4 2 n) (out : Fin w ↪ Fin Ct.R),
              (K₁ * μ * n ≤ (Ct.depth : ℝ) ∧ (Ct.depth : ℝ) ≤ K₂ * μ * n) ∧
              (K₁ * (w + w * μ) * (n : ℝ) ^ 8 ≤ (Ct.width : ℝ) ∧
                (Ct.width : ℝ) ≤ K₂ * (w + w * μ) * (n : ℝ) ^ 8) ∧
              decodeOut D out (run (by norm_num : 2 ≤ 4) rule₁ rule₂ Ct 0) = idealOut C ∧
              (∀ p : ℝ, 0 < p → p < p₀ → ∀ ν : PMF (FaultPattern Ct), IsLocalStochastic Ct ν p →
                failProb (by norm_num : 2 ≤ 4) rule₁ rule₂ C Ct D out ν ≤
                  ENNReal.ofReal (A * ((w : ℝ) * μ * n) ^ k * p ^ (c * n))) ∧
              (C.IsIdentity → ∀ t, Ct.layer t = Layer.logical [] ∨ Ct.layer t = Layer.sweep []) := by sorry

end LocalSweepFT
