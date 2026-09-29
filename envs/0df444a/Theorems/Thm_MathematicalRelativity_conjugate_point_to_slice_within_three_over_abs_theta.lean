-- Prove2me | Theorems.Thm_MathematicalRelativity_conjugate_point_to_slice_within_three_over_abs_theta
-- name    : MathematicalRelativity.conjugate_point_to_slice_within_three_over_abs_theta
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T15:18:47.973455+00:00
-- url     : https://prove2.me/theorems/59c1b153-92f3-4530-a586-850dc4b765ff
-- title:
--   Conjugate point to a spacelike hypersurface within proper time $3/|\theta_0|$
-- statement:
--   Let $(M,g)$ satisfy the strong energy condition, let $S$ be a spacelike hypersurface and let $c$ be a future-pointing unit timelike geodesic leaving $S$ orthogonally at proper time $0$ and defined at least up to proper time $3/|\theta_0|$. If the expansion of the congruence of timelike geodesics orthogonal to $S$ satisfies $\theta \le \theta_0 < 0$ at the point where $c$ meets $S$, then $c$ contains a point conjugate to $S$ at proper time at most $3/|\theta_0|$.
-- source:
--   J. Natário, Mathematical Relativity, arXiv:2003.02855, p. 73, Chapter 4, Theorem 3.5 (with Theorem 3.2)

import Definitions.Def_natario_gr_core
import Definitions.Def_natario_gr_curves
import Definitions.Def_natario_gr_congruence
import Definitions.Def_natario_gr_causality

namespace MathematicalRelativity

theorem conjugate_point_to_slice_within_three_over_abs_theta
    (m : Spacetime) (S : Slice m) (c : ℝ → Pt) (T theta0 : ℝ)
    (hsec : m.StrongEnergyCondition)
    (hgeo : m.IsUnitTimelikeGeodesicOn c (Set.Icc 0 T))
    (horth : S.OrthogonalAt c 0)
    (hneg : theta0 < 0)
    (hexp : S.expansion (c 0) ≤ theta0)
    (hT : 3 / (-theta0) ≤ T) :
    ∃ t ∈ Set.Ioc (0:ℝ) (3 / (-theta0)), S.ConjugateToSlice c 0 t := by
  sorry

end MathematicalRelativity
