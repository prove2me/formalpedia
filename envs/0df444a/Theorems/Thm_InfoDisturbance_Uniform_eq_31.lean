-- Prove2me | Theorems.Thm_InfoDisturbance_Uniform_eq_31
-- name    : InfoDisturbance.Uniform.eq_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:26.748157+00:00
-- url     : https://prove2.me/theorems/cd0c8fd3-0a7d-458a-bfad-34b0211af539
-- title:
--   Eq. (31), p. 12 — Haar average of two squared overlaps
-- statement:
--   Let $\Omega$ be the unitarily invariant probability measure on unit vectors of $\mathbb C^d$, $d\ge1$. For any unit vectors $|a\rangle,|b\rangle\in\mathbb C^d$, not necessarily orthogonal or equal,
--   $$\int d\Omega_\psi\,|\langle\psi|a\rangle|^2\,|\langle\psi|b\rangle|^2=\frac{1+|\langle a|b\rangle|^2}{d(d+1)} .$$
--
--   The paper takes this from Eq. (12) of Jones and uses it to evaluate the three nonzero classes of matrix elements in the proof of Lemma 9.
--
--   **Formalization Note** $\Omega$ is the published `haarPureStateLaw d hd`; the inner product is Mathlib's, conjugate-linear in the first argument, so `inner ℂ ψ a` is $\langle\psi|a\rangle$.
-- source:
--   Barnum, Information-disturbance tradeoff in quantum measurement on the uniform ensemble, arXiv:quant-ph/0205155v1, p. 12, Eq. (31) (citing Jones [27], Eq. (12))

import Mathlib
import Definitions.Def_InfoDisturbance_Uniform_Model
open scoped Matrix ComplexOrder Kronecker
open QAlgorithms QAlgorithms.QuditFidelity MeasureTheory

namespace InfoDisturbance.Uniform

theorem eq_31 (d : ℕ) (hd : 0 < d) (a b : EuclideanSpace ℂ (Fin d)) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ∫ ψ, ‖inner ℂ ψ a‖ ^ 2 * ‖inner ℂ ψ b‖ ^ 2 ∂haarPureStateLaw d hd
      = (1 + ‖inner ℂ a b‖ ^ 2) / ((d : ℝ) * ((d : ℝ) + 1)) := by sorry

end InfoDisturbance.Uniform
