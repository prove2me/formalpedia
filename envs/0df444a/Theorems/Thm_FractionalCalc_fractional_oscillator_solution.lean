-- Prove2me | Theorems.Thm_FractionalCalc_fractional_oscillator_solution
-- name    : FractionalCalc.fractional_oscillator_solution
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T16:45:40.837411+00:00
-- url     : https://prove2.me/theorems/fcf73464-bdb9-4d35-a410-6bc55dd8197b
-- title:
--   Solution of the Caputo fractional harmonic oscillator (§5.2)
-- statement:
--   Let $1<\alpha\le2$, $\omega>0$, and $x_0,x_1\in\mathbb R$. The function
--   $$x(t)=x_0\,E_\alpha(-\omega^\alpha t^\alpha)+x_1\,t\,E_{\alpha,2}(-\omega^\alpha t^\alpha)$$
--   satisfies the Caputo fractional harmonic oscillator equation
--   $${}^{C}D_{0+}^{\alpha}x(t)+\omega^\alpha x(t)=0\qquad(t>0),$$
--   with initial conditions $x(0)=x_0$ and $x'(0)=x_1$. This is the capstone result of §5.2 of the source, obtained by the Laplace transform; at $\alpha=2$ it reduces to the classical oscillator $x(t)=x_0\cos\omega t+(x_1/\omega)\sin\omega t$.
--
--   **Formalization Note** The printed solution in the source omits the factor $t$ in the second term; the paper's own Laplace derivation $F(s)=x_0 s^{-1}/(1+\omega^\alpha s^{-\alpha})+x_1 s^{-2}/(1+\omega^\alpha s^{-\alpha})$ together with Eq. (26) at $\beta=2$ gives the factor $t$, which is formalized here. The equation uses $\omega^\alpha$ (the paper's fractional oscillator equation).
-- source:
--   F. G. Rodrigues & E. C. de Oliveira, Rev. Bras. Ens. Fís. 37(3), 3305 (2015), https://doi.org/10.1590/S1806-11173731842, §5.2, solution of ${}^{C}D^\alpha x+\omega^\alpha x=0$, $1<\alpha\le2$. The factor $t$ in the second term is restored per the paper's Laplace derivation and Eq. (26) ($\beta=2$).

import Mathlib
import Definitions.Def_FractionalCalc_rlIntegral
import Definitions.Def_FractionalCalc_caputoDeriv
import Definitions.Def_FractionalCalc_mittagLeffler
open MeasureTheory Set Classical

namespace FractionalCalc
theorem fractional_oscillator_solution (α ω : ℝ) (x0 x1 : ℝ)
    (hα1 : 1 < α) (hα2 : α ≤ 2) (hω : 0 < ω) :
    let x : ℝ → ℝ := fun t => x0 * mittagLefflerOne α (-(ω ^ α) * t ^ α)
      + x1 * t * mittagLeffler α 2 (-(ω ^ α) * t ^ α)
    (∀ t > 0, caputoDeriv 0 α x t + ω ^ α * x t = 0) ∧ x 0 = x0 ∧ deriv x 0 = x1 := by sorry
end FractionalCalc
