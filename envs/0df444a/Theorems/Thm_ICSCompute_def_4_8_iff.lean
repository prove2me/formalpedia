-- Prove2me | Theorems.Thm_ICSCompute_def_4_8_iff
-- name    : ICSCompute.def_4_8_iff
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:50:23.964362+00:00
-- url     : https://prove2.me/theorems/115c9d06-522d-4599-8b9a-e54f2224ea28
-- title:
--   Definition 4.8 — a unitary circuit is a pure PMG iff condition (4.2)
-- statement:
--   Let $C$ be a unitary circuit on $n + r$ qubits with matrix $U_C$, whose first $n$ qubits are the single-qubit feedback registers $R = (R_1,\dots,R_n)$. Then $(n, C)$ is a pure PMG if and only if, for every choice of auxiliary registers $E = (E_1,\dots,E_n)$ and every family of unitaries $V_i$ acting on $R_i, E_i$,
--   $$\operatorname{Tr}_R\Big[\Big(\bigotimes_{i=1}^n V_i\Big)\big(U_C\otimes I_{H_E}\big)\Big] \ \text{ is unitary.} \tag{4.2}$$
--   Corresponding feedback input and output registers are identified, each operator acts as the identity on registers it does not mention, and the auxiliary registers remain external.
--
--   The criterion replaces validity against all local channels (Definition 4.4) by unitarity of one operator for each choice of local unitaries; it is the form in which validity is proved in §6.
--
--   Differences from the source:
--   - encoding: general quantum circuits over {H, T, T†, CNOT, SWAP, Tof} with measurements, |0⟩ ancillas, discarding and classical control (p.14) → QCirc: a gate list over the same gate set on the inputs plus |0⟩ ancillas, output = the first wires, the rest discarded; reason: deferred measurement turns measurement and classical control into gates on fresh ancillas without changing the channel, and a unitary circuit's matrix is its work-|0⟩ block (p.14), so every source circuit has a QCirc with the same channel and matrix
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), Definition 4.8, eq. (4.2), p.21 (PDF p.23)

import Mathlib
import Definitions.Def_ICSCompute_IsPurePMG
import Definitions.Def_ICSCompute_connectU

namespace ICSCompute

open QAlgorithms

/-- **Definition 4.8, equivalence (4.2)** (Shmueli, *What Can Be Computed with Indefinite Causal
Structure?*, arXiv:2610.40573, version of 2026-11-03, sha256 d3e36399…b606, Definition 4.8,
p.21 (PDF p.23)).

"For a unitary circuit `C` with matrix `U_C`, the pair `(n, C)` is a pure PMG if and only if the
following condition holds. … For every choice of auxiliary registers `E := (E₁, …, Eₙ)` and local
unitaries `Vᵢ` acting on `Rᵢ, Eᵢ`, `Tr_R[(⨂ᵢ Vᵢ)(U_C ⊗ I_{H_E})]` is unitary. (4.2)"

**Formalization Note** `C` is an `(n + r)`-qubit unitary circuit whose first `n` qubits are the
feedback registers; `U_C = C.mat` (work wires returned to `|0⟩`, §3, p.14) is split as
`S(n) ⊗ S(r)` by `splitQ`. The auxiliary registers are qubit registers `Eᵢ = S(e i)` of any
size, including zero. `Tr_R[(⨂ᵢ Vᵢ)(U_C ⊗ I_E)]` is `connectU`, an operator on `S(r) ⊗ E`. -/
theorem def_4_8_iff {n r : ℕ} (C : Desc n r r) (hC : C.IsUnitary) :
    IsPurePMG C ↔
      ∀ (e : Fin n → ℕ) (V : (i : Fin n) → Matrix (Bool × Qubits (e i)) (Bool × Qubits (e i)) ℂ),
        (∀ i, V i ∈ Matrix.unitaryGroup (Bool × Qubits (e i)) ℂ) →
          connectU (Matrix.reindex (splitQ n r) (splitQ n r) C.mat) V ∈
            Matrix.unitaryGroup (Qubits r × ((i : Fin n) → Qubits (e i))) ℂ := by sorry

end ICSCompute
