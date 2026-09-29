-- Prove2me | Theorems.Thm_MathematicalRelativity_not_maximizing_after_conjugate_point
-- name    : MathematicalRelativity.not_maximizing_after_conjugate_point
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-15T15:21:25.122677+00:00
-- url     : https://prove2.me/theorems/a01ceee1-a19e-4903-b097-c51a31ee6a28
-- title:
--   A geodesic stops maximizing past a conjugate point
-- statement:
--   If a future-pointing unit timelike geodesic $c$ leaves the spacelike hypersurface $S$ orthogonally and has a point conjugate to $S$ strictly before its endpoint $c(T)$, then $c$ does not maximize proper time among future-pointing timelike curves from $S$ to $c(T)$: some such curve is strictly longer.
-- source:
--   J. Natário, Mathematical Relativity, arXiv:2003.02855, p. 73, Chapter 4, Theorem 3.6 (see also Theorem 3.3)

import Definitions.Def_natario_gr_core
import Definitions.Def_natario_gr_curves
import Definitions.Def_natario_gr_congruence
import Definitions.Def_natario_gr_causality

namespace MathematicalRelativity

theorem not_maximizing_after_conjugate_point
    (m : Spacetime) (S : Slice m) (c : ℝ → Pt) (T tstar : ℝ)
    (hgeo : m.IsUnitTimelikeGeodesicOn c (Set.Icc 0 T))
    (horth : S.OrthogonalAt c 0)
    (ht : tstar ∈ Set.Ioo (0:ℝ) T)
    (hconj : S.ConjugateToSlice c 0 tstar) :
    ¬ S.MaximizesFromSlice c T := by
  sorry

end MathematicalRelativity
