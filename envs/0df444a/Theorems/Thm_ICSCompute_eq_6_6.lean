-- Prove2me | Theorems.Thm_ICSCompute_eq_6_6
-- name    : ICSCompute.eq_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:48:10.671209+00:00
-- url     : https://prove2.me/theorems/16b48647-9617-431a-94c0-e3a1859ef1cf
-- title:
--   Eq. (6.6) — $T_{\mathbf V}$ on $|y\rangle_Q\otimes|\eta\rangle_E$
-- statement:
--   Let $U_C$ be the operator (6.4) built from $h$ and the $U_{i,a}$, let $V_i$ be operators on $R_i, E_i$, $B_{i,a} := V_i(U_{i,a}\otimes I_{E_i})$, and $T_{\mathbf V} := \operatorname{Tr}_R[(\bigotimes_i V_i)(U_C\otimes I_E)]$. For every $y\in\{0,1\}^n$ and every vector $|\eta\rangle$ of $E$,
--   $$T_{\mathbf V}\big(|y\rangle_Q\otimes|\eta\rangle_E\big) = \sum_{r\in\{0,1\}^n} |r\rangle_Q\otimes\Big(\bigotimes_{i=1}^n B^{r_i,y_i}_{i,h_i(r)}\Big)|\eta\rangle_E. \tag{6.6}$$
--
--   This expansion shows that the input and output of $Q$ determine the operator applied to the auxiliary registers, which is what makes the block-wise unitarity argument possible.
--
--   Differences from the source:
--   - generalization: unitary V_i on qubit auxiliary registers E_i, unitary U_{i,a}, h with (6.2) → arbitrary operators V_i, U_{i,a}, arbitrary finite index types E_i, any h; reason: the identity is algebraic and uses none of these hypotheses; the paper's setting is a special case
--   - generalization: n ∈ ℕ (positive integers; the paper writes ℕ ∪ {0} when 0 is allowed, p.19) → n : ℕ, including n = 0; reason: the n = 0 instance is true (a single vertex, trivial registers); every positive n is an instance
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), proof of Theorem 6.1, eq. (6.6), p.33 (PDF p.35)

import Mathlib
import Definitions.Def_ICSCompute_Tmat

namespace ICSCompute

open QAlgorithms

/-- **Eq. (6.6)** (Shmueli, *What Can Be Computed with Indefinite Causal Structure?*,
arXiv:2610.40573, version of 2026-11-03, sha256 d3e36399…b606, proof of Theorem 6.1, eq. (6.6),
p.33 (PDF p.35)).

With `U_C` as in (6.4), `Vᵢ` operators on `Rᵢ, Eᵢ`, `B_{i,a} := Vᵢ (U_{i,a} ⊗ I_{Eᵢ})` and
`T_V := Tr_R[(⨂ᵢ Vᵢ)(U_C ⊗ I_E)]`: for every `y ∈ {0,1}ⁿ` and every vector `|η⟩` of `E`,
`T_V (|y⟩_Q ⊗ |η⟩_E) = ∑_{r ∈ {0,1}ⁿ} |r⟩_Q ⊗ (⨂ᵢ B^{rᵢ,yᵢ}_{i,hᵢ(r)}) |η⟩_E`.

**Formalization Note** The auxiliary registers `Eᵢ` are arbitrary finite index types (qubit
registers are a special case), and the identity holds for arbitrary operators `Vᵢ`, `U_{i,a}`
and any `h`, so no unitarity or (6.2) hypothesis is stated. Vectors are functions on the index
type; `|y⟩_Q ⊗ |η⟩_E` is `(q, ε) ↦ [q = y] η(ε)`. -/
theorem eq_6_6 {n : ℕ} {E : Fin n → Type*} [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (V : (i : Fin n) → Matrix (Bool × E i) (Bool × E i) ℂ)
    (U : Fin n → Bool → Matrix Bool Bool ℂ) (h : Qubits n → Qubits n)
    (y : Qubits n) (η : ((i : Fin n) → E i) → ℂ) :
    Matrix.mulVec (TV V U h) (fun p => (if p.1 = y then 1 else 0) * η p.2) =
      ∑ r : Qubits n, fun p : Qubits n × ((i : Fin n) → E i) =>
        (if p.1 = r then 1 else 0) * (Matrix.mulVec (Bprod V U h r y) η) p.2 := by sorry

end ICSCompute
