-- Prove2me | Theorems.Thm_InfoDisturbance_Uniform_theorem_8
-- name    : InfoDisturbance.Uniform.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:27.494102+00:00
-- url     : https://prove2.me/theorems/3a77d74d-0f47-446f-8c3c-859edf1c886f
-- title:
--   Theorem 8, p. 11 — the one-term square-root dynamics is optimal, with average fidelity (d + Σ_b (tr F_b^{1/2})²)/(d(d+1))
-- statement:
--   Let $\{F_b\}_{b\in B}$ be a POVM on $\mathbb C^d$, $d\ge1$, and let $\{\mathcal A_b\}$ be operations compatible with it in which each $\mathcal A_b$ has a single operator: $\mathcal A_b(\rho)=A_b\rho A_b^\dagger$ with $A_b^\dagger A_b=F_b$. Let $\Omega$ be the unitarily invariant probability measure on unit vectors, and $F(|\psi\rangle\langle\psi|,\sigma)=\langle\psi|\sigma|\psi\rangle$. Then
--   $$\sum_b\int d\Omega_\psi\,F\big(|\psi\rangle\langle\psi|,\mathcal A_b(|\psi\rangle\langle\psi|)\big)\;\le\;\sum_b\int d\Omega_\psi\,F\big(|\psi\rangle\langle\psi|,F_b^{1/2}|\psi\rangle\langle\psi|F_b^{1/2}\big)\;=\;\frac{1}{d(d+1)}\Big(d+\sum_b\big(\operatorname{tr}F_b^{1/2}\big)^2\Big).$$
--
--   So among one-term instruments for a given POVM the square-root dynamics has the largest average fidelity, and its value gives the minimal disturbance $\overline D_{\min}=1-\overline F_{\max}$ (Eqs. (34)–(35)).
--
--   **Formalization Note** $\int d\Omega_\psi F(\cdot,\cdot)$ for one outcome is `averageFidelity d hd (conjSuperop (A b))`. The printed (25) lacks a closing parenthesis; the bracketing used is that of (34). $\operatorname{tr}F_b^{1/2}$ is real and taken as a real part.
-- source:
--   Barnum, Information-disturbance tradeoff in quantum measurement on the uniform ensemble, arXiv:quant-ph/0205155v1, p. 11, Theorem 8, Eq. (25); value as in Eq. (34), p. 13

import Mathlib
import Definitions.Def_InfoDisturbance_Uniform_Model
open scoped Matrix ComplexOrder Kronecker
open QAlgorithms QAlgorithms.QuditFidelity MeasureTheory

namespace InfoDisturbance.Uniform

theorem theorem_8 (d : ℕ) (hd : 0 < d) {B : Type*} [Fintype B]
    (F : B → Matrix (Fin d) (Fin d) ℂ) (hF : IsPOVM F)
    (A : B → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ b, (A b)ᴴ * A b = F b) :
    ∑ b, averageFidelity d hd (conjSuperop (A b))
        ≤ ∑ b, averageFidelity d hd (conjSuperop (cfc Real.sqrt (F b))) ∧
      ∑ b, averageFidelity d hd (conjSuperop (cfc Real.sqrt (F b)))
        = (1 / ((d : ℝ) * ((d : ℝ) + 1))) *
            ((d : ℝ) + ∑ b, ((cfc Real.sqrt (F b)).trace.re) ^ 2) := by sorry

end InfoDisturbance.Uniform
