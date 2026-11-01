-- Prove2me | Theorems.Thm_HeisenbergRep_Knill_knill_theorem
-- name    : HeisenbergRep.Knill.knill_theorem
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:03:12.037745+00:00
-- url     : https://prove2.me/theorems/f08f2b04-e9e2-424e-8fb2-56e8c29be68f
-- title:
--   Theorem 1 (Knill's theorem): Clifford gates, Pauli measurements and classically controlled Clifford operations are perfectly simulated in randomized classical polynomial time
-- statement:
--   Let $F$ be any uniform family of $n$-qubit quantum computers performing only (a) Clifford group gates, (b) measurements of Pauli group operators, and (c) Clifford group operations conditioned on classical bits, which may be the results of earlier measurements: a polynomial-time classical controller with polynomially many random bits that, at each of polynomially many steps, chooses from the transcript of earlier outcomes an arbitrary Clifford gate $U\in N(\mathcal P)$ or the measurement of a Pauli operator $\pm P$.
--
--   Then there is a randomized polynomial-time classical algorithm $\mathcal A$ (a polynomial-time multi-stack Turing machine fed its input followed by polynomially many uniform random bits), chosen before $n$ and $x$, such that for every $n$ and every input basis state $|x\rangle$, $x\in\{0,1\}^n$, there is a distribution $\mu$ on pairs (transcript, tableau $T=(T_1,\dots,T_n)$ of Pauli operators) with
--
--   1. every $T$ in the support of $\mu$ a valid stabilizer description: phases $\pm1$, pairwise commuting, independent, $-I$ not generated;
--   2. the output of $\mathcal A$ on $(n,x)$ distributed as the code (transcript code followed by tableau code) of a sample of $\mu$;
--   3. the joint law of
--   $$\Bigl(\text{transcript},\ \prod_{j=1}^n\tfrac12(I+T_j)\Bigr)\quad\text{under }\mu$$
--   equal to the joint law of the quantum computer's measurement record and its final state $|\psi_{\mathrm{final}}\rangle\langle\psi_{\mathrm{final}}|$.
--
--   For a valid tableau, $\prod_j\tfrac12(I+T_j)$ is the projector onto the unique state stabilized by $T$, so $\mathcal A$ samples the record and the final state of the quantum computer exactly. In particular quantum computation can only be more powerful than classical computation through gates outside the Clifford group.
--
--   The statement implies the Open platform theorem `QAlgorithms.DeWolf.gottesmanKnill` (de Wolf's Gottesman–Knill theorem), obtained by restricting the gates to Pauli, $H$, $S$, CNOT and the measurements to phase $+1$, and keeping only the final state.
--
--   Differences from the source:
--   - reading: perfectly simulated → the sampler's output encodes (transcript, valid tableau) and the joint law of (transcript, Π_j ½(I + T_j)) equals F.recordDist n x; reason: the strongest of the readings record only / final state only / both; the state is compared as a density matrix since a global phase is unobservable
--   - reading: any quantum computer … in polynomial time on a probabilistic classical computer → a uniform GKFamily on input |x⟩, and a RandPolyTimeSampler (poly-time TM2 machine plus uniform random bits) chosen before n and x; reason: a single algorithm must work for all sizes; every stabilizer state is one Clifford gate away from a basis state
--   - generalization: Clifford group gates → any U ∈ Clifford.normalizer n, given to the controller's code by its images of X_q and Z_q; reason: covers R(j), P(j), CNOT(j → k) and all their products
--   - reading: measurements of Pauli group operators → measurements of A = ±P (phase exponent 0 or 2) with P± = ½(I ± A) and Born probabilities; reason: for phase ±i, ½(I ± A) are not projectors and A has imaginary eigenvalues (p. 9)
--   - generalization: Clifford group operations conditioned on classical bits, which may be the results of earlier measurements → the controller sees its random bits and the whole transcript and may choose any next operation, including which operator to measure; reason: conditioning a fixed Clifford operation on bits is a special case
--   - encoding: the classical record of measurement results → transcript with an entry none per gate step and some β per measurement, β = false for the result +1; reason: the gate entries are determined by the controller; no instance changes
-- source:
--   Gottesman, The Heisenberg Representation of Quantum Computers, arXiv:quant-ph/9807006v1, §8, Theorem 1, p. 19 (proof sketch pp. 17–19)

import Mathlib
import Definitions.Def_HeisenbergRep_Knill_GKFamily

namespace HeisenbergRep.Knill

open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.Complexity

/-- **Theorem 1 (Knill's theorem): Clifford gates, Pauli measurements and classically controlled
Clifford operations are perfectly simulated in polynomial time on a probabilistic classical
computer.**
Gottesman, *The Heisenberg Representation of Quantum Computers*, arXiv:quant-ph/9807006v1, §8,
Theorem 1, p. 19: "Any quantum computer performing only: a) Clifford group gates, b) measurements
of Pauli group operators, and c) Clifford group operations conditioned on classical bits, which may
be the results of earlier measurements, can be perfectly simulated in polynomial time on a
probabilistic classical computer."

For every uniform family `F` of such computers (`GKFamily`: a polynomial-time classical controller
with polynomially many random bits that, from the transcript of earlier outcomes, chooses at each of
polynomially many steps an arbitrary Clifford gate `U ∈ N(P)` or the measurement of a signed
Hermitian Pauli operator `±P`) there is a randomized polynomial-time classical algorithm `A`, fixed
before `n` and `x`, such that for every number of qubits `n` and every input basis state `|x⟩` the
output of `A` on `(n, x)` is distributed as the code of a pair (transcript, stabilizer tableau `T`)
whose law `μ` satisfies
1. every `T` in the support of `μ` is a valid stabilizer description (`n` independent, commuting
   Pauli operators with phases `±1`, `−I` not generated);
2. `A`'s output law is the image of `μ` under the code `encHist ⊗ encodeTableau`;
3. the law of (transcript, `Π_j ½(I + T_j)`) under `μ` equals the joint law `F.recordDist n x` of
   the quantum computer's measurement record and its final state `|ψ_final⟩⟨ψ_final|`.

**Formalization Note.**
* (R1, reading) "Perfectly simulated" is read as exact equality of the *joint* law of the
  classical record and the final state, the strongest of the three readings (record only, final
  state only, both). The final state is compared as a density matrix (no global phase); for a valid
  tableau, `Π_j ½(I + T_j)` is the projector onto the unique state it stabilizes.
* (R2, reading) "Any quantum computer … in polynomial time on a probabilistic classical computer":
  a uniform family `F`, input `|x⟩` with `x ∈ {0,1}^n`, and a `RandPolyTimeSampler` (a
  polynomial-time multi-stack Turing machine run on the input `encInput n x` followed by
  polynomially many uniform random bits); the sampler is chosen before `n` and `x`.
* (R3, generalization) Gates are all elements of the Clifford group `N(P)`, communicated by the
  controller through their images of `X_q`, `Z_q` (`GKOp.code`).
* (R4, reading) Measured operators are the Hermitian Pauli operators `±P` (phase `±1`), with the
  projectors `P± = ½(I ± A)` of Eq. (35) and Born probabilities; the outcome `false` is `+1`.
* (R5, generalization) The controller sees its random bits and the whole transcript and may choose
  any next operation, including which operator to measure.
* The transcript has an entry `none` for each gate step.

This statement implies the Open `QAlgorithms.DeWolf.gottesmanKnill` (de Wolf's Gottesman–Knill
theorem): restrict the gates to Pauli, `H`, `S`, `CNOT`, the measurements to phase `+1`, and take
the second marginal. -/
theorem knill_theorem :
    ∀ F : GKFamily, ∃ A : RandPolyTimeSampler, ∀ (n : ℕ) (x : Qubits n),
      ∃ μ : PMF (List (Option Bool) × Tableau n),
        (∀ p ∈ μ.support, IsValidTableau p.2) ∧
        A.outDist (encInput n x) = μ.map (fun p => encHist p.1 ++ encodeTableau p.2) ∧
        μ.map (fun p => (p.1, tableauProjector p.2)) = F.recordDist n x := by sorry

end HeisenbergRep.Knill
