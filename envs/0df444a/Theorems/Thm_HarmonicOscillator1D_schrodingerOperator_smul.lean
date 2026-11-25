-- Prove2me | Theorems.Thm_HarmonicOscillator1D_schrodingerOperator_smul
-- name    : HarmonicOscillator1D.schrodingerOperator_smul
-- status  : Proved
-- author  : @LG
-- created : 2026-11-25T01:56:03.648255+00:00
-- url     : https://prove2.me/theorems/b681edab-ad0f-5109-8722-16296b43fa6f
-- title:
--   Homogeneity of the Schrödinger operator
-- statement:
--   The Schrödinger operator is **homogeneous** for complex scalars on twice-differentiable wavefunctions. For $c\in\mathbb C$ and $\psi:\mathbb R\to\mathbb C$ differentiable with differentiable derivative,
--   $$H(c\,\psi)=c\,H\psi.$$
--   Together with additivity this establishes linearity of the Schrödinger operator.
--
--   **Formalization Note.** In Lean the scalar is `c : ℂ`, the hypotheses are `Differentiable ℝ ψ` and `Differentiable ℝ (deriv ψ)`, and the conclusion is `Q.schrodingerOperator (c • ψ) = c • Q.schrodingerOperator ψ`.
-- source:
--   https://github.com/leanprover-community/physlib/blob/85bb8f5df598f6701be57a70f06e08069e30589c/Physlib/QuantumMechanics/HarmonicOscillator/OneDimension/Basic.lean#L201-L212 (lemma `schrodingerOperator_smul`; ℏ made a positive parameter)

import Mathlib
import Definitions.Def_HO1D_basic

namespace HarmonicOscillator1D
theorem schrodingerOperator_smul (Q : HarmonicOscillator) (c : ℂ) (ψ : ℝ → ℂ)
    (hψ : Differentiable ℝ ψ) (hψ' : Differentiable ℝ (deriv ψ)) :
    Q.schrodingerOperator (c • ψ) = c • Q.schrodingerOperator ψ := by sorry
end HarmonicOscillator1D
