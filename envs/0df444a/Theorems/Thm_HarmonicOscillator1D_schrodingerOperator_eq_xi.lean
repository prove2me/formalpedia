-- Prove2me | Theorems.Thm_HarmonicOscillator1D_schrodingerOperator_eq_xi
-- name    : HarmonicOscillator1D.schrodingerOperator_eq_xi
-- status  : Open
-- author  : @LG
-- created : 2026-11-25T01:45:22.114867+00:00
-- url     : https://prove2.me/theorems/325c8f4c-b100-59f0-b15e-38bdc74cf45f
-- title:
--   Schrödinger operator in characteristic-length normal form
-- statement:
--   Using the characteristic length $\xi=\sqrt{\hbar/(m\omega)}$, the Schrödinger operator can be written with a single overall prefactor $\hbar^{2}/(2m)$:
--   $$(H\psi)(x)=\frac{\hbar^{2}}{2m}\left(-\psi''(x)+\frac{1}{\xi^{4}}\,x^{2}\psi(x)\right).$$
--   Equivalently the potential coefficient is $(1/\xi^{2})^{2}$. This normal form isolates the dimensional prefactor from the dimensionless differential expression, the standard starting point for solving the oscillator.
--
--   **Formalization Note.** In Lean this is `Q.schrodingerOperator ψ = fun x => (Q.ℏ ^ 2 / (2 * Q.m)) * (-(deriv (deriv ψ) x) + (1 / Q.ξ ^ 2) ^ 2 * x ^ 2 * ψ x)`. It combines the previous normal form with $\xi^{2}=\hbar/(m\omega)$.
-- source:
--   https://github.com/leanprover-community/physlib/blob/85bb8f5df598f6701be57a70f06e08069e30589c/Physlib/QuantumMechanics/HarmonicOscillator/OneDimension/Basic.lean#L166-L174 (lemma `schrodingerOperator_eq_xi`; ℏ made a positive parameter)

import Mathlib
import Definitions.Def_HO1D_basic

namespace HarmonicOscillator1D
theorem schrodingerOperator_eq_xi (Q : HarmonicOscillator) (ψ : ℝ → ℂ) :
    Q.schrodingerOperator ψ =
      fun x => (Q.ℏ ^ 2 / (2 * Q.m)) * (- (deriv (deriv ψ) x) + (1 / Q.ξ ^ 2) ^ 2 * x ^ 2 * ψ x) := by sorry
end HarmonicOscillator1D
