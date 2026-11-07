-- Prove2me | Theorems.Thm_ICSCompute_tv_unitary
-- name    : ICSCompute.tv_unitary
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:48:14.6302+00:00
-- url     : https://prove2.me/theorems/47ed36a7-fd7c-45b3-a8c8-2b503976c23b
-- title:
--   Proof of Theorem 6.1, p.34 — $T_{\mathbf V}T_{\mathbf V}^\dagger = I$
-- statement:
--   Let $h:\{0,1\}^n\to\{0,1\}^n$ satisfy (6.2), let the $U_{i,a}$ be single-qubit unitaries and $U_C$ the operator (6.4), and let $V_i$ be unitaries on $R_i, E_i$ for arbitrary auxiliary registers $E_i$. Then
--   $$T_{\mathbf V}T_{\mathbf V}^\dagger = I_{\mathcal L(H_Q\otimes H_E)},\qquad T_{\mathbf V} := \operatorname{Tr}_R\Big[\Big(\bigotimes_{i=1}^n V_i\Big)\big(U_C\otimes I_{\mathcal L(H_E)}\big)\Big].$$
--
--   Since the $E_i$ and $V_i$ are arbitrary, this is condition (4.2) of Definition 4.8 for the generator of Theorem 6.1, i.e. the validity of the pure process.
--
--   Differences from the source:
--   - generalization: auxiliary registers E_i are qubit registers → E_i arbitrary finite index types; reason: qubit registers are a special case
--   - generalization: n ∈ ℕ (positive integers; the paper writes ℕ ∪ {0} when 0 is allowed, p.19) → n : ℕ, including n = 0; reason: the n = 0 instance is true (a single vertex, trivial registers); every positive n is an instance
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), proof of Theorem 6.1, display after (6.8), p.34 (PDF p.36)

import Mathlib
import Definitions.Def_ICSCompute_IsUSOOutmap
import Definitions.Def_ICSCompute_Tmat

namespace ICSCompute

open QAlgorithms

/-- **`T_V T_V† = I`** (Shmueli, *What Can Be Computed with Indefinite Causal Structure?*,
arXiv:2610.40573, version of 2026-11-03, sha256 d3e36399…b606, proof of Theorem 6.1, display
after (6.8), p.34 (PDF p.36)): "We have proved that the diagonal matrices of `T_V T_V†` are
identities and all its off-diagonal matrices are zero. Consequently, `T_V T_V† = I_{L(H_Q⊗H_E)}`."

Here `h` satisfies (6.2), the `U_{i,a}` are single-qubit unitaries, `U_C` is (6.4), the `Vᵢ` are
unitaries on `Rᵢ, Eᵢ`, and `T_V := Tr_R[(⨂ᵢ Vᵢ)(U_C ⊗ I_E)]`.

**Formalization Note** The auxiliary registers `Eᵢ` are arbitrary finite index types (qubit
registers are a special case). -/
theorem tv_unitary {n : ℕ} {E : Fin n → Type*} [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (h : Qubits n → Qubits n) (hh : Eq62 h)
    (U : Fin n → Bool → Matrix Bool Bool ℂ) (hU : ∀ i a, U i a ∈ Matrix.unitaryGroup Bool ℂ)
    (V : (i : Fin n) → Matrix (Bool × E i) (Bool × E i) ℂ)
    (hV : ∀ i, V i ∈ Matrix.unitaryGroup (Bool × E i) ℂ) :
    TV V U h * (TV V U h).conjTranspose = 1 := by sorry

end ICSCompute
