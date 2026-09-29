-- Prove2me | Theorems.Thm_Gribov_pi3_specialUnitaryGroup
-- name    : Gribov.pi3_specialUnitaryGroup
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T14:18:07.582869+00:00
-- url     : https://prove2.me/theorems/12606f88-b516-40a3-8166-dbde0f5e6461
-- title:
--   $\pi_3(SU(N)) \cong \mathbb{Z}$ for $N \ge 2$
-- statement:
--   For every $N \ge 2$ the third homotopy group of the special unitary group is infinite cyclic:
--   $$\pi_3(SU(N)) \cong \mathbb{Z}.$$
--   This classical computation is one of the homotopy inputs Singer uses (via Toda) in the proof of Theorem 3: for $M = S^3$ it gives $\pi_0(\mathcal{G}_m) \cong \pi_3(SU(N)) = \mathbb{Z}$, whose torsion-freeness forces $\pi_1(\overline{\mathcal{G}}) \neq 0$. Homotopy groups are based at the identity matrix, and the isomorphism is with $\mathbb{Z}$ written multiplicatively.
-- source:
--   I. M. Singer, Some Remarks on the Gribov Ambiguity, Commun. Math. Phys. 60 (1978) 7-12, https://doi.org/10.1007/BF01609471, p. 10, proof of Theorem 3 (citing H. Toda, Composition methods in homotopy groups of spheres, Ann. of Math. Studies 49, 1962)

import Definitions.Def_gribov_gauge_group

open scoped Topology

namespace Gribov

/-- `π₃(SU(N)) ≅ ℤ` for `N ≥ 2`. -/
theorem pi3_specialUnitaryGroup (N : ℕ) (hN : 2 ≤ N) :
    Nonempty (π_ 3 (SU N) 1 ≃* Multiplicative ℤ) := by sorry

end Gribov
