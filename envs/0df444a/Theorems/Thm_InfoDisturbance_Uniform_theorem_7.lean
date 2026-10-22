-- Prove2me | Theorems.Thm_InfoDisturbance_Uniform_theorem_7
-- name    : InfoDisturbance.Uniform.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:33.521996+00:00
-- url     : https://prove2.me/theorems/657c3c5e-13e3-4384-8b22-94beac066eaa
-- title:
--   Theorem 7 (Ando), p. 11 — (A, B) ↦ A^t ⊗ B^{1−t} is jointly concave
-- statement:
--   Let $0\le t\le1$. The map
--   $$(A,B)\;\longmapsto\;A^t\otimes B^{1-t}$$
--   is jointly concave on pairs of positive semidefinite operators, in the Loewner order: for positive semidefinite $A_1,A_2$ (on one space), $B_1,B_2$ (on another) and $0\le\lambda\le1$,
--   $$\big(\lambda A_1+(1-\lambda)A_2\big)^t\otimes\big(\lambda B_1+(1-\lambda)B_2\big)^{1-t}\;\succeq\;\lambda\,A_1^t\otimes B_1^{1-t}+(1-\lambda)\,A_2^t\otimes B_2^{1-t}.$$
--
--   This theorem of Ando is equivalent to Lieb's concavity theorem; the paper uses its special case $A=B$, $t=1/2$ to prove Proposition 6.
--
--   **Formalization Note** "$X\succeq Y$" is stated as `(X - Y).PosSemidef`; $X^s$ is `matrixRpow X s` (`cfc` of `Real.rpow`), so $X^0=I$ even for singular $X$, which makes the endpoints $t\in\{0,1\}$ statements about linear maps.
-- source:
--   Barnum, Information-disturbance tradeoff in quantum measurement on the uniform ensemble, arXiv:quant-ph/0205155v1, p. 11, Theorem 7 (Ando [22]), Eq. (23)

import Mathlib
import Definitions.Def_InfoDisturbance_Uniform_Model
open scoped Matrix ComplexOrder Kronecker
open QAlgorithms QAlgorithms.QuditFidelity MeasureTheory

namespace InfoDisturbance.Uniform

theorem theorem_7 {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (A₁ A₂ : Matrix ι ι ℂ) (B₁ B₂ : Matrix κ κ ℂ)
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef) (hB₁ : B₁.PosSemidef) (hB₂ : B₂.PosSemidef)
    (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    (matrixRpow (μ • A₁ + (1 - μ) • A₂) t ⊗ₖ matrixRpow (μ • B₁ + (1 - μ) • B₂) (1 - t)
      - (μ • (matrixRpow A₁ t ⊗ₖ matrixRpow B₁ (1 - t))
          + (1 - μ) • (matrixRpow A₂ t ⊗ₖ matrixRpow B₂ (1 - t)))).PosSemidef := by sorry

end InfoDisturbance.Uniform
