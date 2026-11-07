-- Prove2me | Theorems.Thm_ICSCompute_lemma_4_1
-- name    : ICSCompute.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:50:36.738664+00:00
-- url     : https://prove2.me/theorems/ceab20b3-542c-4ad5-8d5b-fd4debeb9a70
-- title:
--   Lemma 4.1 — simplified process-matrix formula for isometries
-- statement:
--   Let $n, r, k\ge 0$ and let $U$ be a unitary on $n+r+k$ qubits. Let $C_{(U,k)}(\rho) := U(\rho\otimes|0^k\rangle\langle0^k|)U^\dagger$ with $H_{AI} = H_{AO} = \mathcal S(n)$, $H_P = \mathcal S(r)$, $H_F = \mathcal S(r+k)$, $W := \mathrm{CJ}(C_{(U,k)})$, and
--   $$U_G := \operatorname{Tr}_{H_{AI}}(U)\in\mathbb C^{2^{r+k}\times 2^{r+k}},$$
--   the partial trace identifying the first $n$ input and output qubits. Then:
--
--   1. $G_{W,AI,AO} = \mathrm{CJ}\big(C_{(U_G,k)}\big)$, where $C_{(U_G,k)}(\sigma) := U_G(\sigma\otimes|0^k\rangle\langle0^k|)U_G^\dagger$ ($U_G$ need not be unitary);
--   2. if $W$ is a process matrix for the single-qubit feedback pairs, then $C_{(U_G,k)}$ is a quantum channel, and any circuit $C$ implementing $C_{(U,k)}$ with the same ordered feedback registers gives a PMG $(n, C)$ with generated channel $\mathrm{PMO}_{(n,C)} = C_{(U_G,k)}$.
--
--   For a unitary generating circuit this identifies the generated channel with conjugation by $\operatorname{Tr}_R(U_C)$, which is how the generated unitary of Theorem 6.1 is computed.
--
--   Differences from the source:
--   - generalization: n, r ∈ ℕ (positive) → n, r : ℕ, including 0; reason: the statement holds verbatim for n = 0 or r = 0 (empty registers, S(0) = ℂ); every positive instance is a special case
--   - encoding: a circuit C implementing C_(U,k) with the same ordered feedback registers → C from n + r to n + (r + k) qubits with C.channel ρ = C_(U,k)(ρ) after re-bracketing n + r + k = n + (r + k); reason: the re-bracketing is the identity on qubit order
--   - encoding: general quantum circuits over {H, T, T†, CNOT, SWAP, Tof} with measurements, |0⟩ ancillas, discarding and classical control (p.14) → QCirc: a gate list over the same gate set on the inputs plus |0⟩ ancillas, output = the first wires, the rest discarded; reason: deferred measurement turns measurement and classical control into gates on fresh ancillas without changing the channel, and a unitary circuit's matrix is its work-|0⟩ block (p.14), so every source circuit has a QCirc with the same channel and matrix
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), Lemma 4.1, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_ICSCompute_IsQuantumChannel
import Definitions.Def_ICSCompute_IsPurePMG
import Definitions.Def_ICSCompute_ancChannel

namespace ICSCompute

open QAlgorithms

/-- **Lemma 4.1 (Simplified PM formula for isometries)** (Shmueli, *What Can Be Computed with
Indefinite Causal Structure?*, arXiv:2610.40573, version of 2026-11-03, sha256 d3e36399…b606,
Lemma 4.1, p.20 (PDF p.22)).

Let `U` be a unitary on `n + r + k` qubits, `C_(U,k)(ρ) := U (ρ ⊗ |0ᵏ⟩⟨0ᵏ|) U†` with
`H_AI = H_AO = S(n)`, `H_P = S(r)`, `H_F = S(r + k)`, `W := CJ(C_(U,k))` and
`U_G := Tr_{H_AI}(U)` (the partial trace identifies the first `n` input and output qubits). Then
`G_{W,AI,AO} = CJ(C_(U_G,k))`. If `W` is a process matrix for the single-qubit feedback pairs,
then `C_(U_G,k)` is a quantum channel, and any circuit `C` implementing `C_(U,k)` with the same
ordered feedback registers gives a PMG `(n, C)` with generated channel `PMO_(n,C) = C_(U_G,k)`.

**Formalization Note** `n, r : ℕ` include `0` (the paper has `n, r ∈ ℕ`). The output
`S(n + r + k)` is split as `S(n) ⊗ S(r + k)` by `splitQ3`; `W` is `CJ(C_(U,k))` with the input
split by `splitQ n r` and the output by `splitQ3`. "A circuit implementing `C_(U,k)`" is a circuit
`C` from `n + r` to `n + (r + k)` qubits whose channel equals `C_(U,k)` after the re-bracketing
`castQ` (the identity on qubit order). -/
theorem lemma_4_1 {n r k : ℕ} (U : Matrix (Qubits (n + r + k)) (Qubits (n + r + k)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits (n + r + k)) ℂ) :
    identityConnection
        (Matrix.reindex (Equiv.prodCongr (splitQ n r) (splitQ3 n r k))
          (Equiv.prodCongr (splitQ n r) (splitQ3 n r k)) (cj (ancChannel k U))) =
      cj (ancChannel k (ptraceR (Matrix.reindex (splitQ3 n r k) (splitQ3 n r k) U))) ∧
    (IsProcessMatrix
        (Matrix.reindex (Equiv.prodCongr (splitQ n r) (splitQ3 n r k))
          (Equiv.prodCongr (splitQ n r) (splitQ3 n r k)) (cj (ancChannel k U))) →
      IsQuantumChannel (ancChannel k (ptraceR (Matrix.reindex (splitQ3 n r k) (splitQ3 n r k) U))) ∧
        ∀ C : Desc n r (r + k),
          (∀ ρ, C.channel ρ = Matrix.reindex (castQ n r k) (castQ n r k) (ancChannel k U ρ)) →
            IsPMG C ∧
              pmoD C = ancChannel k (ptraceR (Matrix.reindex (splitQ3 n r k) (splitQ3 n r k) U))) := by sorry

end ICSCompute
