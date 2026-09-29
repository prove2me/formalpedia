-- Prove2me | Theorems.Thm_MathematicalRelativity_maximizing_geodesic_from_cauchy_slice
-- name    : MathematicalRelativity.maximizing_geodesic_from_cauchy_slice
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-15T15:23:30.992793+00:00
-- url     : https://prove2.me/theorems/e1df1b18-b0a5-4f06-949e-218f56932fa9
-- title:
--   Existence of a maximizing geodesic from a Cauchy hypersurface
-- statement:
--   In a globally hyperbolic spacetime with Cauchy hypersurface $S$, every point $q$ in the chronological future of $S$ is joined to $S$ by a future-pointing timelike geodesic which is orthogonal to $S$, parameterized by proper time, and of maximal proper time among all future-pointing timelike curves from $S$ to $q$.
-- source:
--   J. Natário, Mathematical Relativity, arXiv:2003.02855, pp. 77-78, Chapter 4, Theorem 4.3

import Definitions.Def_natario_gr_core
import Definitions.Def_natario_gr_curves
import Definitions.Def_natario_gr_congruence
import Definitions.Def_natario_gr_causality

namespace MathematicalRelativity

theorem maximizing_geodesic_from_cauchy_slice
    (m : Spacetime) (S : Slice m) (q : Pt)
    (hcauchy : m.IsCauchySurface S.carrier)
    (hq : q ∈ m.chronFuture S.carrier) :
    ∃ (c : ℝ → Pt) (T : ℝ), 0 < T ∧ m.IsUnitTimelikeGeodesicOn c (Set.Icc 0 T) ∧
      S.OrthogonalAt c 0 ∧ c T = q ∧ S.MaximizesFromSlice c T := by
  sorry

end MathematicalRelativity
