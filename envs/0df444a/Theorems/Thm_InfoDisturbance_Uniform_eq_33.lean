-- Prove2me | Theorems.Thm_InfoDisturbance_Uniform_eq_33
-- name    : InfoDisturbance.Uniform.eq_33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:42.869024+00:00
-- url     : https://prove2.me/theorems/90625f92-1f1d-4d18-8648-cb74f6747576
-- title:
--   Eq. (33), pp. 12–13 — average overlap of an operation on the uniform ensemble
-- statement:
--   Let $\Omega$ be the unitarily invariant probability measure on unit vectors of $\mathbb C^d$, $d\ge1$. For any finite family of operators $\{A_k\}_{k\in K}$ on $\mathbb C^d$, the operation $\mathcal E(\rho)=\sum_kA_k\rho A_k^\dagger$ has average overlap
--   $$\int d\Omega_\psi\,\langle\psi|\mathcal E(|\psi\rangle\langle\psi|)|\psi\rangle=\int d\Omega_\psi\sum_k|\langle\psi|A_k|\psi\rangle|^2=\frac{1}{d(d+1)}\sum_k\Big(|\operatorname{tr}A_k|^2+\operatorname{tr}A_kA_k^\dagger\Big).$$
--
--   The page writes this for one operator per outcome ($A_k=A_b$); by (17) the same computation applies term by term to the HK operators $A_{bi}$ of a multi-term instrument. No trace preservation is assumed: the simplification $\sum_k\operatorname{tr}A_kA_k^\dagger=d$ is the next step of the proof of Theorem 8.
--
--   **Formalization Note** The left side is `averageFidelity d hd (krausApply A)`, whose integrand is $\operatorname{Re}\operatorname{tr}(|\psi\rangle\langle\psi|\mathcal E(|\psi\rangle\langle\psi|))$; $\operatorname{tr}A_kA_k^\dagger$ is real and taken as a real part.
-- source:
--   Barnum, Information-disturbance tradeoff in quantum measurement on the uniform ensemble, arXiv:quant-ph/0205155v1, pp. 12–13, Eq. (33)

import Mathlib
import Definitions.Def_InfoDisturbance_Uniform_Model
open scoped Matrix ComplexOrder Kronecker
open QAlgorithms QAlgorithms.QuditFidelity MeasureTheory

namespace InfoDisturbance.Uniform

theorem eq_33 (d : ℕ) (hd : 0 < d) {K : Type*} [Fintype K]
    (E : K → Matrix (Fin d) (Fin d) ℂ) :
    averageFidelity d hd (krausApply E)
      = (1 / ((d : ℝ) * ((d : ℝ) + 1))) *
          ∑ k, (‖(E k).trace‖ ^ 2 + (E k * (E k)ᴴ).trace.re) := by sorry

end InfoDisturbance.Uniform
