-- Prove2me | Theorems.Thm_MathematicalRelativity_penrose_singularity_theorem
-- name    : MathematicalRelativity.penrose_singularity_theorem
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-15T15:36:33.77365+00:00
-- url     : https://prove2.me/theorems/237091ec-150d-455a-88a5-643d199bca33
-- title:
--   Penrose's singularity theorem
-- statement:
--   **Penrose (1965).** Let $(M,g)$ be a connected globally hyperbolic spacetime with a noncompact Cauchy hypersurface $S$, satisfying the null energy condition. If $S$ contains a trapped surface — a compact two-dimensional surface $\Sigma \subset S$ whose two families of orthogonal null geodesics both have negative expansion — then $(M,g)$ is singular, i.e. geodesically incomplete.
--
--   The proof combines null focusing (a conjugate point to $\Sigma$ within affine parameter $2/|\theta_0|$), the fact that past a conjugate point the null geodesic enters $I^{+}(\Sigma)$, and a topological argument: $\partial I^{+}(\Sigma)$ would be compact and homeomorphic to the noncompact $S$, a contradiction.
-- source:
--   J. Natário, Mathematical Relativity, arXiv:2003.02855, pp. 84-85, Chapter 4, Theorem 6.5

import Definitions.Def_natario_gr_core
import Definitions.Def_natario_gr_curves
import Definitions.Def_natario_gr_congruence
import Definitions.Def_natario_gr_causality

namespace MathematicalRelativity

theorem penrose_singularity_theorem
    (m : Spacetime) (S : Slice m) (Sig : Surface m S)
    (hcauchy : m.IsCauchySurface S.carrier)
    (hnoncompact : ¬ IsCompact S.carrier)
    (hnec : m.NullEnergyCondition)
    (htrapped : Sig.IsTrapped) :
    m.IsSingular := by
  sorry

end MathematicalRelativity
