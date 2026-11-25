-- Prove2me | Theorems.Thm_HarmonicOscillator1D_schrodingerOperator_eq
-- name    : HarmonicOscillator1D.schrodingerOperator_eq
-- status  : Open
-- author  : @LG
-- created : 2026-11-25T01:41:14.013246+00:00
-- url     : https://prove2.me/theorems/7d862806-a32b-43c6-8e37-476862fc32b4
-- title:
--   Schrödinger operator as kinetic plus potential scalar multiples
-- statement:
--   The **Schrödinger operator** of the oscillator acts on a wavefunction $\psi:\mathbb R\to\mathbb C$ by
--   $$(H\psi)(x)=-\frac{\hbar^{2}}{2m}\,\psi''(x)+\frac{1}{2}m\omega^{2}x^{2}\psi(x).$$
--   This theorem rewrites $H$ as a sum of two real-scalar multiples of functions: a kinetic part and a multiplication-by-$x^{2}$ potential part,
--   $$H\psi=\left(-\frac{\hbar^{2}}{2m}\right)\!\cdot\psi''+\left(\frac{1}{2}m\omega^{2}\right)\!\cdot\bigl(x\mapsto x^{2}\bigr)\,\psi,$$
--   where the scalar multiples are the real scalar action on complex-valued functions and $x^{2}$ is embedded into $\mathbb C$.
--
--   **Formalization Note.** In Lean the right-hand side uses `•` (real scalar multiplication on `ℝ → ℂ`), `deriv (deriv ψ)` for $\psi''$, and `Complex.ofReal x ^ 2` for the real-to-complex embedding of $x^{2}$.
-- source:
--   https://github.com/leanprover-community/physlib/blob/85bb8f5df598f6701be57a70f06e08069e30589c/Physlib/QuantumMechanics/HarmonicOscillator/OneDimension/Basic.lean#L156-L163 (lemma `schrodingerOperator_eq`; ℏ made a positive parameter)

import Mathlib
import Definitions.Def_HO1D_basic

namespace HarmonicOscillator1D
theorem schrodingerOperator_eq (Q : HarmonicOscillator) (ψ : ℝ → ℂ) :
    Q.schrodingerOperator ψ = (- Q.ℏ ^ 2 / (2 * Q.m)) • (deriv (deriv ψ)) +
      (1/2 * Q.m * Q.ω^2) • ((fun x => Complex.ofReal x ^ 2) * ψ) := by sorry
end HarmonicOscillator1D
