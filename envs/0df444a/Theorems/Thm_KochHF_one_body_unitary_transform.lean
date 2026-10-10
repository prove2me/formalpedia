-- Prove2me | Theorems.Thm_KochHF_one_body_unitary_transform
-- name    : KochHF.one_body_unitary_transform
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:26:29.396985+00:00
-- url     : https://prove2.me/theorems/12aef6d9-3da8-4a7e-945d-3f64056a253c
-- title:
--   Fock-space unitaries $e^{i\lambda\hat M}$ fix the vacuum and rotate creators (Eqs. (57), (59))
-- statement:
--   Let $M$ be a hermitian $K\times K$ matrix, $\hat M=\sum_{\alpha\beta}M_{\alpha\beta}c^\dagger_\alpha c_\beta$ and $\lambda\in\mathbb R$. Then
--   $$e^{i\lambda\hat M}|0\rangle=|0\rangle\qquad\text{and}\qquad e^{i\lambda\hat M}\,c^\dagger_\gamma\,e^{-i\lambda\hat M}=\sum_\alpha c^\dagger_\alpha\,\bigl(e^{i\lambda M}\bigr)_{\alpha\gamma}$$
--   for every reference orbital $\gamma$.
--
--   Consequently $\hat U(\lambda)=e^{i\lambda\hat M}$ maps Slater determinants to Slater determinants formed in the rotated orbital basis; this is the family of variations used in Hartree-Fock theory.
-- source:
--   E. Koch, *Mean-Field Theory: Hartree-Fock and BCS*, in E. Pavarini, E. Koch, J. van den Brink, G. Sawatzky (eds.), Quantum Materials: Experiments and Theory, Modeling and Simulation Vol. 6, Forschungszentrum Jülich, 2016, ISBN 978-3-95806-159-0, http://www.cond-mat.de/events/correl16, Sec. 3.2, p. 2.16, Eqs. (55)–(59).

import Mathlib
import Definitions.Def_KochHF_FockSpace

open Matrix

namespace KochHF

theorem one_body_unitary_transform {K : ℕ} (M : Matrix (Fin K) (Fin K) ℂ) (hM : M.IsHermitian)
    (t : ℝ) (γ : Fin K) :
    NormedSpace.exp ((Complex.I * t) • oneBodyOp M) *ᵥ vacuum K = vacuum K ∧
    NormedSpace.exp ((Complex.I * t) • oneBodyOp M) * cdag γ *
        NormedSpace.exp ((-(Complex.I * t)) • oneBodyOp M) =
      ∑ a, NormedSpace.exp ((Complex.I * t) • M) a γ • cdag a := by sorry

end KochHF
