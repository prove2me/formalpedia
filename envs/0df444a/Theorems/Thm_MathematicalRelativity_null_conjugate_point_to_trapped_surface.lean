-- Prove2me | Theorems.Thm_MathematicalRelativity_null_conjugate_point_to_trapped_surface
-- name    : MathematicalRelativity.null_conjugate_point_to_trapped_surface
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T15:35:43.345049+00:00
-- url     : https://prove2.me/theorems/0f2506eb-71e6-41f8-ab7c-88dd831080d6
-- title:
--   Conjugate point to a two-surface along a null normal geodesic
-- statement:
--   Let $(M,g)$ be a globally hyperbolic spacetime satisfying the null energy condition, $S$ a Cauchy hypersurface, $\Sigma \subset S$ a compact two-dimensional surface with unit normal $n$ inside $S$, and $p \in \Sigma$ a point where the expansion of the null geodesics with initial condition $N + n$ is $\theta \le \theta_0 < 0$. Then the null geodesic $c_p$ issuing from $p$ with initial condition $N_p + n_p$ contains a point conjugate to $\Sigma$ at affine parameter distance at most $2/|\theta_0|$ to the future of $\Sigma$, provided it extends that far.
-- source:
--   J. Natário, Mathematical Relativity, arXiv:2003.02855, pp. 81-82, Chapter 4, Proposition 6.2

import Definitions.Def_natario_gr_core
import Definitions.Def_natario_gr_curves
import Definitions.Def_natario_gr_congruence
import Definitions.Def_natario_gr_causality

namespace MathematicalRelativity

theorem null_conjugate_point_to_trapped_surface
    (m : Spacetime) (S : Slice m) (Sig : Surface m S) (c : ℝ → Pt) (T theta0 : ℝ)
    (hcauchy : m.IsCauchySurface S.carrier)
    (hnec : m.NullEnergyCondition)
    (hgeo : m.IsNullGeodesicOn c (Set.Icc 0 T))
    (hstart : Sig.NormalNullGeodesicAt Sig.lplus c 0)
    (hneg : theta0 < 0)
    (hexp : Sig.thetaPlus (c 0) ≤ theta0)
    (hT : 2 / (-theta0) ≤ T) :
    ∃ t ∈ Set.Ioc (0:ℝ) (2 / (-theta0)), Sig.ConjugateToSurface Sig.lplus c 0 t := by
  sorry

end MathematicalRelativity
