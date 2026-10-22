-- Prove2me | Theorems.Thm_InfoDisturbance_Uniform_proposition_6
-- name    : InfoDisturbance.Uniform.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:27.999142+00:00
-- url     : https://prove2.me/theorems/997b9a0a-fc70-42bb-986c-662fe8949a51
-- title:
--   Proposition 6, p. 10 — ⟨ψ|P₁|ψ⟩² + ⟨ψ|P₂|ψ⟩² ≤ ⟨ψ|√(P₁² + P₂²)|ψ⟩²
-- statement:
--   For any vector $|\psi\rangle\in\mathbb C^d$ and positive semidefinite operators $P_1,P_2$ on $\mathbb C^d$,
--   $$\langle\psi|P_1|\psi\rangle^2+\langle\psi|P_2|\psi\rangle^2\;\le\;\langle\psi|\sqrt{P_1^2+P_2^2}\,|\psi\rangle^2 .\tag{18}$$
--
--   Iterating (18) coarse-grains any multi-term instrument into the square-root operation without decreasing the average fidelity, which is the last step of the proof of Theorem 5. No bound $\sqrt{P_1^2+P_2^2}\le I$ is assumed (the paper notes it is not needed).
--
--   **Formalization Note** $\langle\psi|P|\psi\rangle$ is real for positive $P$ and is taken as `(inner ℂ ψ (act P ψ)).re`; $\sqrt{\cdot}$ is `cfc Real.sqrt`. $|\psi\rangle$ need not be normalized, as on the page ("for any $|\psi\rangle$").
-- source:
--   Barnum, Information-disturbance tradeoff in quantum measurement on the uniform ensemble, arXiv:quant-ph/0205155v1, p. 10, Proposition 6, Eq. (18)

import Mathlib
import Definitions.Def_InfoDisturbance_Uniform_Model
open scoped Matrix ComplexOrder Kronecker
open QAlgorithms QAlgorithms.QuditFidelity MeasureTheory

namespace InfoDisturbance.Uniform

theorem proposition_6 {d : ℕ} (ψ : EuclideanSpace ℂ (Fin d))
    (P₁ P₂ : Matrix (Fin d) (Fin d) ℂ) (hP₁ : P₁.PosSemidef) (hP₂ : P₂.PosSemidef) :
    (inner ℂ ψ (act P₁ ψ)).re ^ 2 + (inner ℂ ψ (act P₂ ψ)).re ^ 2
      ≤ (inner ℂ ψ (act (cfc Real.sqrt (P₁ * P₁ + P₂ * P₂)) ψ)).re ^ 2 := by sorry

end InfoDisturbance.Uniform
