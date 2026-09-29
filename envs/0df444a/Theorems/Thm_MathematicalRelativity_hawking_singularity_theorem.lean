-- Prove2me | Theorems.Thm_MathematicalRelativity_hawking_singularity_theorem
-- name    : MathematicalRelativity.hawking_singularity_theorem
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T15:23:57.485106+00:00
-- url     : https://prove2.me/theorems/921d3c0a-687e-4750-9dbb-28b7c64b92f1
-- title:
--   Hawking's singularity theorem
-- statement:
--   **Hawking (1966).** Let $(M,g)$ be a globally hyperbolic spacetime satisfying the strong energy condition, and suppose that the expansion of the congruence of future-pointing timelike geodesics orthogonal to a Cauchy hypersurface $S$ satisfies $\theta \le \theta_0 < 0$ everywhere on $S$. Then $(M,g)$ is singular, that is, geodesically incomplete: no future-directed timelike geodesic orthogonal to $S$ can be extended to proper time greater than $3/|\theta_0|$ to the future of $S$.
-- source:
--   J. Natário, Mathematical Relativity, arXiv:2003.02855, p. 79, Chapter 4, Theorem 5.2

import Definitions.Def_natario_gr_core
import Definitions.Def_natario_gr_curves
import Definitions.Def_natario_gr_congruence
import Definitions.Def_natario_gr_causality

namespace MathematicalRelativity

theorem hawking_singularity_theorem
    (m : Spacetime) (S : Slice m) (theta0 : ℝ)
    (hcauchy : m.IsCauchySurface S.carrier)
    (hsec : m.StrongEnergyCondition)
    (hneg : theta0 < 0)
    (hexp : ∀ x ∈ S.carrier, S.expansion x ≤ theta0) :
    m.IsSingular := by
  sorry

end MathematicalRelativity
