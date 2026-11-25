-- Prove2me | Theorems.Thm_HarmonicOscillator1D_schrodingerOperator_add
-- name    : HarmonicOscillator1D.schrodingerOperator_add
-- status  : Open
-- author  : @LG
-- created : 2026-11-25T01:50:38.407983+00:00
-- url     : https://prove2.me/theorems/ac751535-5d50-5926-a794-75322c1627ff
-- title:
--   Additivity of the Schrödinger operator
-- statement:
--   The Schrödinger operator is **additive** on twice-differentiable wavefunctions. If $\psi,\varphi:\mathbb R\to\mathbb C$ are differentiable with differentiable derivatives, then
--   $$H(\psi+\varphi)=H\psi+H\varphi.$$
--   Together with homogeneity this says the Schrödinger operator is a linear operator on the space of sufficiently regular wavefunctions.
--
--   **Formalization Note.** In Lean the hypotheses are `Differentiable ℝ ψ`, `Differentiable ℝ (deriv ψ)` and the analogous ones for `φ`; the conclusion is `Q.schrodingerOperator (ψ + φ) = Q.schrodingerOperator ψ + Q.schrodingerOperator φ`. The differentiability assumptions are needed because `deriv` is only additive under differentiability.
-- source:
--   https://github.com/leanprover-community/physlib/blob/85bb8f5df598f6701be57a70f06e08069e30589c/Physlib/QuantumMechanics/HarmonicOscillator/OneDimension/Basic.lean#L186-L198 (lemma `schrodingerOperator_add`; ℏ made a positive parameter)

import Mathlib
import Definitions.Def_HO1D_basic

namespace HarmonicOscillator1D
theorem schrodingerOperator_add (Q : HarmonicOscillator) (ψ φ : ℝ → ℂ)
    (hψ : Differentiable ℝ ψ) (hψ' : Differentiable ℝ (deriv ψ))
    (hφ : Differentiable ℝ φ) (hφ' : Differentiable ℝ (deriv φ)) :
    Q.schrodingerOperator (ψ + φ) = Q.schrodingerOperator ψ + Q.schrodingerOperator φ := by sorry
end HarmonicOscillator1D
