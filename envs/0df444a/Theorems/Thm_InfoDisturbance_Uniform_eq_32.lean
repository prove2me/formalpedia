-- Prove2me | Theorems.Thm_InfoDisturbance_Uniform_eq_32
-- name    : InfoDisturbance.Uniform.eq_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:35.070153+00:00
-- url     : https://prove2.me/theorems/a4c83a33-9a5c-414d-9f1b-bbebc2f9f230
-- title:
--   Eq. (32), p. 12 — Haar average of a product of two quadratic forms
-- statement:
--   Let $\Omega$ be the unitarily invariant probability measure on unit vectors of $\mathbb C^d$, $d\ge1$, and $\Pi$ its second moment (Eq. (26)). For all operators $A,B$ on $\mathbb C^d$,
--   $$\int d\Omega_\psi\,\langle\psi|A|\psi\rangle\langle\psi|B|\psi\rangle=\operatorname{tr}\big(\Pi(A\otimes B)\big)=\frac{1}{d(d+1)}\sum_{i,j}\Big(\langle i|A|i\rangle\langle j|B|j\rangle+\langle i|A|j\rangle\langle j|B|i\rangle\Big).$$
--
--   The second form equals $(\operatorname{tr}A\operatorname{tr}B+\operatorname{tr}AB)/(d(d+1))$; with $B=A^\dagger$ it gives the average overlap (33).
--
--   **Formalization Note** $\langle\psi|A|\psi\rangle$ is `inner ℂ ψ (act A ψ)`; $\langle i|A|j\rangle$ is the matrix entry `A i j`. Both equalities are stated, as on the page.
-- source:
--   Barnum, Information-disturbance tradeoff in quantum measurement on the uniform ensemble, arXiv:quant-ph/0205155v1, p. 12, Eq. (32) and the sentence following it

import Mathlib
import Definitions.Def_InfoDisturbance_Uniform_Model
open scoped Matrix ComplexOrder Kronecker
open QAlgorithms QAlgorithms.QuditFidelity MeasureTheory

namespace InfoDisturbance.Uniform

theorem eq_32 (d : ℕ) (hd : 0 < d) (A B : Matrix (Fin d) (Fin d) ℂ) :
    ∫ ψ, inner ℂ ψ (act A ψ) * inner ℂ ψ (act B ψ) ∂haarPureStateLaw d hd
        = (secondMoment d hd * (A ⊗ₖ B)).trace ∧
      ∫ ψ, inner ℂ ψ (act A ψ) * inner ℂ ψ (act B ψ) ∂haarPureStateLaw d hd
        = (1 / ((d : ℂ) * ((d : ℂ) + 1))) *
            ∑ i : Fin d, ∑ j : Fin d, (A i i * B j j + A i j * B j i) := by sorry

end InfoDisturbance.Uniform
