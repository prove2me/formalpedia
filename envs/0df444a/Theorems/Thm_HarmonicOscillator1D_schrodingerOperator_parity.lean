-- Prove2me | Theorems.Thm_HarmonicOscillator1D_schrodingerOperator_parity
-- name    : HarmonicOscillator1D.schrodingerOperator_parity
-- status  : Open
-- author  : @LG
-- created : 2026-11-25T02:01:13.498873+00:00
-- url     : https://prove2.me/theorems/b8a8e38f-a5a3-4a79-93b2-7ce93a27a740
-- title:
--   The Schrödinger operator commutes with parity
-- statement:
--   The **parity operator** sends a wavefunction to its reflection, $(P\psi)(x)=\psi(-x)$. This theorem states that the Schrödinger operator of the harmonic oscillator **commutes with parity**: for every $\psi:\mathbb R\to\mathbb C$,
--   $$H(P\psi)=P(H\psi).$$
--   Physically, the harmonic-oscillator Hamiltonian is invariant under spatial reflection $x\mapsto -x$, because the potential $\tfrac12 m\omega^{2}x^{2}$ is even and the second derivative is reflection-equivariant. This is the structural reason the oscillator's eigenfunctions can be chosen of definite parity.
--
--   **Formalization Note.** In Lean this is `Q.schrodingerOperator (parityOperator ψ) = parityOperator (Q.schrodingerOperator ψ)` with `parityOperator ψ = fun x => ψ (-x)`. No differentiability hypothesis is needed: the proof uses the reflection rule for `deriv`, which holds unconditionally.
-- source:
--   https://github.com/leanprover-community/physlib/blob/85bb8f5df598f6701be57a70f06e08069e30589c/Physlib/QuantumMechanics/HarmonicOscillator/OneDimension/Basic.lean#L177-L183 (lemma `schrodingerOperator_parity`; ℏ made a positive parameter)

import Mathlib
import Definitions.Def_HO1D_basic

namespace HarmonicOscillator1D
theorem schrodingerOperator_parity (Q : HarmonicOscillator) (ψ : ℝ → ℂ) :
    Q.schrodingerOperator (parityOperator ψ) = parityOperator (Q.schrodingerOperator ψ) := by sorry
end HarmonicOscillator1D
