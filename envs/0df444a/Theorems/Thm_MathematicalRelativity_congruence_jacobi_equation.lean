-- Prove2me | Theorems.Thm_MathematicalRelativity_congruence_jacobi_equation
-- name    : MathematicalRelativity.congruence_jacobi_equation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T14:38:09.674238+00:00
-- url     : https://prove2.me/theorems/4f63aece-a5b3-4320-9894-2b80a6761373
-- title:
--   Geodesic deviation vectors satisfy the Jacobi equation
-- statement:
--   Let $X$ be the tangent field of a congruence of unit timelike geodesics and let $c$ be one of its integral curves. If a vector field $Y$ along $c$ is transported according to $\nabla_X Y^{\mu} = B^{\mu}{}_{\nu}Y^{\nu}$ — the relation satisfied by the deviation vector of a one-parameter family of geodesics of the congruence — then $Y$ solves the Jacobi equation
--   $$ \nabla_X\nabla_X Y = R(X, Y)X . $$
-- source:
--   J. Natário, Mathematical Relativity, arXiv:2003.02855, pp. 64-65, Chapter 4, Propositions 1.2 and 1.3

import Definitions.Def_natario_gr_core
import Definitions.Def_natario_gr_curves
import Definitions.Def_natario_gr_congruence
import Definitions.Def_natario_gr_causality

namespace MathematicalRelativity

theorem congruence_jacobi_equation
    (m : Spacetime) (K : Congruence m) (c Y : ℝ → Pt) (I : Set ℝ)
    (hI : IsOpen I)
    (hc : K.IsIntegralCurveOn c I)
    (hY : ∀ a, ContDiffOn ℝ 2 (fun s => Y s a) I)
    (hdev : ∀ t ∈ I, ∀ a, m.covDAlong c Y t a
      = ∑ al, ∑ nu, m.ginv (c t) a al * K.B al nu (c t) * Y t nu) :
    m.IsJacobiFieldOn c Y I := by
  sorry

end MathematicalRelativity
