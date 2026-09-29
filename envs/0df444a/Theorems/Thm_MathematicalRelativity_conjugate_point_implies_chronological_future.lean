-- Prove2me | Theorems.Thm_MathematicalRelativity_conjugate_point_implies_chronological_future
-- name    : MathematicalRelativity.conjugate_point_implies_chronological_future
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-15T15:36:03.771114+00:00
-- url     : https://prove2.me/theorems/c48bb4cb-795a-4fd9-bae8-463e0156c43c
-- title:
--   Past a conjugate point a null normal geodesic enters the chronological future of the surface
-- statement:
--   Let $(M,g)$ be globally hyperbolic with Cauchy hypersurface $S$, let $\Sigma \subset S$ be a compact two-surface and let $c$ be the null geodesic leaving $\Sigma$ orthogonally in the direction $N + n$. If $c$ has a point conjugate to $\Sigma$ strictly between its initial point and $c(T)$, then $c(T)$ lies in the chronological future $I^{+}(\Sigma)$ of the surface: the broken null curve through the conjugate point can be deformed into a timelike curve.
-- source:
--   J. Natário, Mathematical Relativity, arXiv:2003.02855, p. 83, Chapter 4, Proposition 6.3

import Definitions.Def_natario_gr_core
import Definitions.Def_natario_gr_curves
import Definitions.Def_natario_gr_congruence
import Definitions.Def_natario_gr_causality

namespace MathematicalRelativity

theorem conjugate_point_implies_chronological_future
    (m : Spacetime) (S : Slice m) (Sig : Surface m S) (c : ℝ → Pt) (T tstar : ℝ)
    (hcauchy : m.IsCauchySurface S.carrier)
    (hgeo : m.IsNullGeodesicOn c (Set.Icc 0 T))
    (hstart : Sig.NormalNullGeodesicAt Sig.lplus c 0)
    (ht : tstar ∈ Set.Ioo (0:ℝ) T)
    (hconj : Sig.ConjugateToSurface Sig.lplus c 0 tstar) :
    c T ∈ m.chronFuture Sig.carrier := by
  sorry

end MathematicalRelativity
