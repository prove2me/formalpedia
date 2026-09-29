-- Prove2me | Theorems.Thm_MathematicalRelativity_congruence_second_fundamental_form_evolution
-- name    : MathematicalRelativity.congruence_second_fundamental_form_evolution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T14:05:15.338913+00:00
-- url     : https://prove2.me/theorems/a23a0adf-47f9-4e0d-9643-7ce2b5aa94a2
-- title:
--   Evolution of the second fundamental form of a geodesic congruence
-- statement:
--   For a unit timelike geodesic congruence with unit tangent field $X$, the second fundamental form $B_{\mu\nu} = \nabla_\nu X_\mu$ satisfies
--   $$ X^{\alpha}\nabla_{\alpha} B_{\mu\nu} \;=\; -\,B_{\mu\alpha}B^{\alpha}{}_{\nu} \;-\; R_{\gamma\mu\alpha\nu}\,X^{\gamma}X^{\alpha}. $$
--   Here $R_{abcd} = g_{ae}R^{e}{}_{bcd}$ is the Riemann tensor with all indices lowered, in the convention $(R(u,v)w)^a = R^a{}_{bcd}w^b u^c v^d$. This is the transport equation from which both the Jacobi equation and the Raychaudhuri equation follow; up to the symmetries of the curvature tensor it is the identity $\nabla_X B_{\mu\nu} = -B_{\mu\alpha}B^{\alpha}{}_{\nu} + R_{\alpha\nu\mu\beta}X^{\alpha}X^{\beta}$ of the source.
-- source:
--   J. Natário, Mathematical Relativity, arXiv:2003.02855, p. 63, Chapter 4, Proposition 1.1

import Definitions.Def_natario_gr_core
import Definitions.Def_natario_gr_curves
import Definitions.Def_natario_gr_congruence
import Definitions.Def_natario_gr_causality

namespace MathematicalRelativity

theorem congruence_second_fundamental_form_evolution
    (m : Spacetime) (K : Congruence m) (x : Pt) (u v : Fin 4) :
    ∑ a, K.X x a * m.covT2 K.B a u v x
      = - (∑ al, ∑ be, K.B u al x * m.ginv x al be * K.B be v x)
        - ∑ ga, ∑ al, m.riemannLower ga u al v x * K.X x ga * K.X x al := by
  sorry

end MathematicalRelativity
