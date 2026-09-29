-- Prove2me | Theorems.Thm_Gribov_pi4_specialUnitaryGroup_trivial
-- name    : Gribov.pi4_specialUnitaryGroup_trivial
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T14:19:13.374028+00:00
-- url     : https://prove2.me/theorems/ac880311-f9dd-4bff-9d24-c728b7ea5ecb
-- title:
--   $\pi_4(SU(N)) = 0$ for $N \ge 3$
-- statement:
--   For every $N \ge 3$ the fourth homotopy group of the special unitary group vanishes:
--   $$\pi_4(SU(N)) = 0 .$$
--   Singer uses this in the proof of Theorem 3 for $M = S^4$: it gives $\pi_0(\mathcal{G}_m) = \pi_4(SU(N)) = 0$ for $N > 2$, which is what makes $\pi_1(\overline{\mathcal{G}})$ the nonvanishing group in that case. Homotopy groups are based at the identity matrix; vanishing is formalized as the group having at most one element.
-- source:
--   I. M. Singer, Some Remarks on the Gribov Ambiguity, Commun. Math. Phys. 60 (1978) 7-12, https://doi.org/10.1007/BF01609471, p. 10, proof of Theorem 3 (citing H. Toda, Composition methods in homotopy groups of spheres, Ann. of Math. Studies 49, 1962)

import Definitions.Def_gribov_gauge_group

open scoped Topology

namespace Gribov

/-- `π₄(SU(N)) = 0` for `N ≥ 3`. -/
theorem pi4_specialUnitaryGroup_trivial (N : ℕ) (hN : 3 ≤ N) :
    Subsingleton (π_ 4 (SU N) 1) := by sorry

end Gribov
