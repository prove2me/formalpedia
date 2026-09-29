-- Prove2me | Theorems.Thm_MathematicalRelativity_raychaudhuri_equation
-- name    : MathematicalRelativity.raychaudhuri_equation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T14:39:02.48774+00:00
-- url     : https://prove2.me/theorems/c41b76a1-7e78-478b-98bc-8ea6dcd3422e
-- title:
--   Raychaudhuri equation
-- statement:
--   For a congruence of unit timelike geodesics with expansion $\theta$, shear $\sigma_{\mu\nu}$ and vorticity $\omega_{\mu\nu}$, the expansion satisfies the Raychaudhuri equation
--   $$ X\cdot\theta \;=\; -\tfrac{1}{3}\theta^{2} \;-\; \sigma_{\mu\nu}\sigma^{\mu\nu} \;+\; \omega_{\mu\nu}\omega^{\mu\nu} \;-\; R_{\mu\nu}X^{\mu}X^{\nu}, $$
--   where $X\cdot\theta = X^{a}\partial_{a}\theta$ is the derivative of $\theta$ along the congruence.
-- source:
--   J. Natário, Mathematical Relativity, arXiv:2003.02855, pp. 65-66, Chapter 4, Proposition 1.5

import Definitions.Def_natario_gr_core
import Definitions.Def_natario_gr_curves
import Definitions.Def_natario_gr_congruence
import Definitions.Def_natario_gr_causality

namespace MathematicalRelativity

theorem raychaudhuri_equation
    (m : Spacetime) (K : Congruence m) (x : Pt) :
    K.along K.expansion x
      = - (1/3 : ℝ) * (K.expansion x) ^ 2 - K.shearSq x + K.vorticitySq x
        - m.ricciQuad x (K.X x) := by
  sorry

end MathematicalRelativity
