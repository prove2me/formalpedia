-- Prove2me | Theorems.Thm_InfoDisturbance_Uniform_coarse_graining
-- name    : InfoDisturbance.Uniform.coarse_graining
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:25.393111+00:00
-- url     : https://prove2.me/theorems/991873c6-6323-4d32-a83b-4dea7e5af38e
-- title:
--   p. 10, proof of Theorem 5 — repeated coarse-graining by Eq. (18)
-- statement:
--   For any vector $|\psi\rangle\in\mathbb C^d$ and any finite family $\{P_j\}_{j\in J}$ of positive semidefinite operators on $\mathbb C^d$,
--   $$\sum_j\langle\psi|P_j|\psi\rangle^2\;\le\;\Big\langle\psi\Big|\sqrt{\textstyle\sum_jP_j^2}\,\Big|\psi\Big\rangle^2 .$$
--
--   This is the step of the proof of Theorem 5 in which "any (finite) purportedly better set of operations can be repeatedly coarse-grained in the manner of Equation 18 to arrive at $\sqrt{F_b}\equiv\sqrt{\sum_iP_{bi}^2}$": applied to the positive parts $P_{bi}$ of the HK operators of one outcome.
--
--   **Formalization Note** As in Proposition 6, quadratic forms are real parts and $\sqrt{\cdot}$ is `cfc Real.sqrt`. For empty $J$ both sides are $0$.
-- source:
--   Barnum, Information-disturbance tradeoff in quantum measurement on the uniform ensemble, arXiv:quant-ph/0205155v1, p. 10, proof of Theorem 5, the sentence after Eq. (18)

import Mathlib
import Definitions.Def_InfoDisturbance_Uniform_Model
open scoped Matrix ComplexOrder Kronecker
open QAlgorithms QAlgorithms.QuditFidelity MeasureTheory

namespace InfoDisturbance.Uniform

theorem coarse_graining {d : ℕ} {J : Type*} [Fintype J] (ψ : EuclideanSpace ℂ (Fin d))
    (P : J → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ j, (P j).PosSemidef) :
    ∑ j, (inner ℂ ψ (act (P j) ψ)).re ^ 2
      ≤ (inner ℂ ψ (act (cfc Real.sqrt (∑ j, P j * P j)) ψ)).re ^ 2 := by sorry

end InfoDisturbance.Uniform
