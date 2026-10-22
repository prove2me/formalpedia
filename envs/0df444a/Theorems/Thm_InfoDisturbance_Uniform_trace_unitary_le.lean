-- Prove2me | Theorems.Thm_InfoDisturbance_Uniform_trace_unitary_le
-- name    : InfoDisturbance.Uniform.trace_unitary_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:08.256981+00:00
-- url     : https://prove2.me/theorems/d5e4fca1-b038-43d0-9fe1-50b52b1a87c2
-- title:
--   p. 13, proof of Theorem 8 — max over unitaries V of |tr VA| occurs where VA = √(A†A)
-- statement:
--   Let $A$ be a positive semidefinite operator on $\mathbb C^d$, and let $W$ be a unitary with $WA=\sqrt{A^\dagger A}$. Then for every unitary $V$,
--   $$|\operatorname{tr}VA|\le|\operatorname{tr}WA| .$$
--   That is, the maximum of $|\operatorname{tr}VA|$ over unitaries $V$ is attained wherever $VA=\sqrt{A^\dagger A}$ (for $A\ge0$, in particular at $V=I$).
--
--   The paper cites this from [4] (cf. [21]) and uses it to conclude that, among the operators $A_b=U_bF_b^{1/2}$ with $A_b^\dagger A_b=F_b$, $|\operatorname{tr}A_b|$ is largest at $U_b=I$.
--
--   **Formalization Note** The square root is `cfc Real.sqrt`; unitaries are members of `Matrix.unitaryGroup`.
-- source:
--   Barnum, Information-disturbance tradeoff in quantum measurement on the uniform ensemble, arXiv:quant-ph/0205155v1, p. 13, proof of Theorem 8 (citing [4], cf. [21]); also p. 10

import Mathlib
import Definitions.Def_InfoDisturbance_Uniform_Model
open scoped Matrix ComplexOrder Kronecker
open QAlgorithms QAlgorithms.QuditFidelity MeasureTheory

namespace InfoDisturbance.Uniform

theorem trace_unitary_le {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.PosSemidef)
    (V W : Matrix (Fin d) (Fin d) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) (hWX : W * X = cfc Real.sqrt (Xᴴ * X)) :
    ‖(V * X).trace‖ ≤ ‖(W * X).trace‖ := by sorry

end InfoDisturbance.Uniform
