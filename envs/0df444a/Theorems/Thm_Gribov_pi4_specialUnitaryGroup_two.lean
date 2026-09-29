-- Prove2me | Theorems.Thm_Gribov_pi4_specialUnitaryGroup_two
-- name    : Gribov.pi4_specialUnitaryGroup_two
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T14:21:10.515639+00:00
-- url     : https://prove2.me/theorems/4db3190e-d717-4045-b0bf-d9d3c15b5d3f
-- title:
--   $\pi_4(SU(2)) \cong \mathbb{Z}/2$
-- statement:
--   The fourth homotopy group of $SU(2)$ is cyclic of order two:
--   $$\pi_4(SU(2)) \cong \mathbb{Z}/2 .$$
--   Singer uses this value in the $SU(2)$ cases of Theorems 3, 6 and 7 over $S^4$, where $\pi_0(\mathcal{G}_m) = \pi_4(SU(2)) = \mathbb{Z}/2$ decides whether $-I$ lies in the identity component of the gauge group. Homotopy groups are based at the identity matrix.
-- source:
--   I. M. Singer, Some Remarks on the Gribov Ambiguity, Commun. Math. Phys. 60 (1978) 7-12, https://doi.org/10.1007/BF01609471, p. 10, proofs of Theorems 3 and 6 (citing H. Toda, Composition methods in homotopy groups of spheres, Ann. of Math. Studies 49, 1962)

import Definitions.Def_gribov_gauge_group

open scoped Topology

namespace Gribov

/-- `π₄(SU(2)) ≅ ℤ/2`. -/
theorem pi4_specialUnitaryGroup_two :
    Nonempty (π_ 4 (SU 2) 1 ≃* Multiplicative (ZMod 2)) := by sorry

end Gribov
