-- Prove2me | Theorems.Thm_LocalSweepFT_lemma_6_2
-- name    : LocalSweepFT.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:45:28.645384+00:00
-- url     : https://prove2.me/theorems/fe1f8b8b-bcee-462b-ae31-518aa9ee49bf
-- title:
--   Lemma 6.2 (operator-requested pinned-down version) — for $d',d-d'\ge2$, Toric encoded simulations fail w.p. $\le A(w\mu n)^k(ap^b)^n$
-- statement:
--   **Operator-requested pinned-down version.** The model, which the paper leaves partly informal, is pinned down as listed under the differences below.
--
--   Let $d'\ge2$ and $d-d'\ge2$. There are constants $a,b>0$, $p_0\in(0,1)$, $A>0$ and $k\in\mathbb N$, depending only on $d,d'$, with the following property. Let $n\ge1$ and let $\mathrm{rule}_1,\mathrm{rule}_2$ be sweep rules for the two sectors of the side-$n$ $(d,d')$-Toric code. There is a referee $D$ for its nice encoding such that for every circuit $C$ of depth $\mu\ge1$ and width $w\ge1$ there are a Toric encoded circuit $\tilde C$ whose registers are side-$n$ $(d,d')$-Toric codes and an injective map $\mathrm{out}$ from the qubits of $C$ to its registers such that decoding the noiseless run gives exactly $C(|0^w\rangle\langle0^w|)$ and, for every $p\in(0,p_0)$ and every local stochastic Pauli noise of rate $p$,
--   $$\Pr\big[\text{decoded }\tilde C[E]\ne C(|0^w\rangle\langle0^w|)\big]\le A\,(w\mu n)^k\,(ap^b)^n.$$
--
--   This is the probabilistic core of the main theorem, for general $(d,d')$: once the input is encoded, Toom-contour counting bounds the probability that the sweep cycles let a syndrome cluster grow to linear size.
--
--   Differences from the source:
--   - reading: initialization stage of depth Θ(poly(log n)), "subjected to local stochastic noise", neither proved nor described (p.60) → registers start at t = 0 in exact encoded |0̄⟩, |H⟩, |S⟩, |T⟩ (Def 5.13 item 1) and the first fault layer precedes the first layer; reason: this is the paper's own interface: Lemma 6.2 is stated "after the initialization stage, namely when assuming the given input is encoded" (p.57); the black-box stage has no model in the paper
--   - encoding: Toric encoded circuit (Def 5.13) with gadgets and classical processing described informally (§§4.5–4.6) → hybrid circuit of R registers and nb reliable classical bits; logical layers of logical Paulis, classically controlled logical Paulis and CX, transversal CX, Z- and X-basis measurement into bits, two-bit classical gates; sweep layers of the sweep cycle on every register plus classical gates; depth counts every layer, classical ones included; reason: p.4 ("reliable classical bits and logic"), Def 5.13 item 2, Remark 3.9 (conditional gates) and Fig. 11 (conditional use of |S⟩)
--   - reading: C̃[E] with fault layers between layers (Def 3.4), N_E local stochastic: Pr[S ⊆ Loc(E)] ≤ p^{|S|}, faults Pauli (Def 3.7) → a single-qubit Pauli fault at every (layer, register qubit) location, applied before every layer (m = 1); ν any distribution on fault patterns with Pr[every location of S carries a non-identity Pauli] ≤ p^{|S|}; classical bits never faulty; reason: pp.4, 13–14; m = 1 is the most frequent noise Def 3.4 allows, and Loc(E) = the non-identity locations is the weakest hypothesis on N_E
--   - reading: simulation (Def 6.1): a referee D and a map from qubits to registers; (1) decoded noiseless run equals the states of C; (2) Pr[some register introduces a logical error w.r.t. D] < δ → D a quantum channel from one register to one qubit with D(Enc ρ Enc†) = ρ; decoding traces out all other wires and applies D to each register out j; failure is the event decoded C̃[E] ≠ C(|0^w⟩⟨0^w|); reason: the proof bounds exactly this event (p.58: "if D ∘ C̃[E] ≠ C̃ …"); the logical-error event of Def 6.1 is phrased for Pauli propagations of Clifford circuits and implies it
--   - encoding: measurements of C (Def 3.1) → dephasing channels in the measured basis, outcome kept in the qubit; reason: C has only qubit wires, so its output is a w-qubit state
--   - reading: a sweep rule flips "such an assignment" (Def 4.6), which one unspecified; "a fixed local rule" (p.5) → every pair of sweep rules (one per sector): local rules returning an admissible rooted chain whenever one exists and 0 otherwise; reason: the proofs of Claims 4.26–4.28 use only admissibility, and the algorithm after Claim 4.7 (p.20) is one such rule; the ∀ reading is the stronger one
--   - encoding: S′ ⊂ S of size d′ "fixed in advance" (Def 4.36) → S′ = {1_1, …, 1_{d′}}; reason: all choices are equivalent under the coordinate-permuting symmetry of the torus
--   - encoding: referee D: L(H^{⊗N}) → L(H^{⊗N}) (Def 6.1) → a channel in Choi–Kraus form (WildeQIT.QChannel, trace preserving) from one register to one qubit; reason: a referee is applied register by register (Def 6.1 (1)); the output qubits carry the logical state
--   - reading: ∀ N_E (p < p₀) ∃ C̃ simulating C with probability 1 − O(poly(w, µ, n))(ap^b)^n → ∃ a b p₀ A k, ∀ n ≥ 1, ∀ sweep rules, ∃ D, ∀ w µ ≥ 1, ∀ C, ∃ C̃ out, ∀ p < p₀, ∀ ν, Pr[fail] ≤ A·(wµn)^k·(a·p^b)^n; reason: C̃, D and out do not depend on the noise in the construction (p.57), so choosing them first is stronger; O(poly) as A(wµn)^k
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Lemma 6.2, p.57

import Mathlib
import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_LocalSweepFT_xLog
import Definitions.Def_LocalSweepFT_IsSweepRule
import Definitions.Def_LocalSweepFT_encMat
import Definitions.Def_LocalSweepFT_IdealCircuit
import Definitions.Def_LocalSweepFT_ToricEncodedCircuit
import Definitions.Def_LocalSweepFT_failProb

namespace LocalSweepFT

/-- Lemma 6.2, p.57 (Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…)), operator-requested pinned-down version. For any `d, d′`
with `d′ ≥ 2`, `d − d′ ≥ 2` there are constants `a, b > 0`, `p₀ ∈ (0, 1)` (and the constants of the
`O(poly)`) depending only on `d, d′` such that: for every side length `n ≥ 1` and every pair of sweep
rules, there is a referee `D` for the nice encoding, and for every circuit `C` of depth `µ ≥ 1` and
width `w ≥ 1` there is a Toric encoded circuit `C̃` whose registers are side-`n` `(d, d′)`-Toric codes,
together with an injective map `out` from the qubits of `C` to the registers of `C̃`, such that the
noiseless run of `C̃` decodes to `C(|0^w⟩⟨0^w|)` and, for every local stochastic Pauli noise of rate
`p < p₀`, the decoded noisy run differs from `C(|0^w⟩⟨0^w|)` with probability at most
`A·(wµn)^k·(a p^b)^n`.

**Formalization Note.** The model is pinned down as follows: the registers start in their encoded
resource states and the first fault layer precedes the first layer ("after the initialization
stage, namely when assuming the given input is encoded"); a Pauli fault layer precedes every layer;
the failure event is exact inequality of the decoded output; `C̃`, `D` and `out` are chosen before
the noise; every pair of sweep rules is allowed; `S′ = {1_1, …, 1_{d′}}`. -/
theorem lemma_6_2 (d d' : ℕ) (h1 : 2 ≤ d') (h2 : 2 ≤ d - d') :
    ∃ a b p₀ A : ℝ, 0 < a ∧ 0 < b ∧ 0 < p₀ ∧ p₀ < 1 ∧ 0 < A ∧ ∃ k : ℕ,
      ∀ (n : ℕ) [NeZero n] (rule₁ : LocalRule d d') (rule₂ : LocalRule d (d - d')),
        IsSweepRule (ZMod n) rule₁ → IsSweepRule (ZMod n) rule₂ →
        ∃ D : WildeQIT.QChannel (QCell d d' n → ZMod 2) (Fin 1 → ZMod 2),
          IsReferee (Sfix (by omega : d' ≤ d)) D ∧
          ∀ (w μ : ℕ), 1 ≤ w → 1 ≤ μ → ∀ C : IdealCircuit w μ,
            ∃ (Ct : ToricEncodedCircuit d d' n) (out : Fin w ↪ Fin Ct.R),
              decodeOut D out (run (by omega : d' ≤ d) rule₁ rule₂ Ct 0) = idealOut C ∧
              ∀ p : ℝ, 0 < p → p < p₀ → ∀ ν : PMF (FaultPattern Ct), IsLocalStochastic Ct ν p →
                failProb (by omega : d' ≤ d) rule₁ rule₂ C Ct D out ν ≤
                  ENNReal.ofReal (A * ((w : ℝ) * μ * n) ^ k * (a * p ^ b) ^ n) := by sorry

end LocalSweepFT
