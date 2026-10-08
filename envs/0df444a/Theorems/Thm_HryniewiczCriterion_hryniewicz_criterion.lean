-- Prove2me | Theorems.Thm_HryniewiczCriterion_hryniewicz_criterion
-- name    : HryniewiczCriterion.hryniewicz_criterion
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-05T21:31:55.318764+00:00
-- url     : https://prove2.me/theorems/5b1c2cb7-b2f6-47c1-aa02-cc4e6b4d72f3
-- title:
--   Hryniewicz's criterion: a prime orbit bounds a disk-like global section iff it is unknotted with $\operatorname{sl}=-1$
-- statement:
--   Let $H:\mathbb{R}^4\to\mathbb{R}$ be smooth with $S=H^{-1}(1)$ strictly star-shaped, and assume the Hamiltonian flow of $X_H$ on $S$, a positive reparametrization of the Reeb flow of $\lambda_0|_S$, is dynamically convex. Then for every prime periodic orbit $\bar P$ on $S$,
--   $$\bar P\ \text{bounds a disk-like global surface of section}\iff\bar P\ \text{is unknotted and}\ \operatorname{sl}(\bar P)=-1.$$
--
--   No non-degeneracy assumption is made. The criterion reduces the existence of a disk-like global section, a global dynamical property, to a topological check on the orbit.
--
--   **Formalization Note** Hryniewicz states the theorem for any dynamically convex contact form on $S^3$. Such a form is tight, and every tight contact form on $S^3$ is diffeomorphic to $\lambda_0|_S$ on a star-shaped $S$ (Eliashberg). That reduction is not part of this statement; Hryniewicz makes the same reduction at the start of Section 3. The flow is that of $X_H$, which has the same orbits, global sections, unknots, self-linking numbers and indices as the Reeb flow.
-- source:
--   Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, https://arxiv.org/abs/1105.2077, Theorem 1.7, p. 3, first sentence

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

namespace HryniewiczCriterion

/-- Hryniewicz's criterion (Theorem 1.7): for a dynamically convex flow on a strictly
star-shaped energy surface in `ℝ⁴`, a prime periodic orbit bounds a disk-like global
surface of section if and only if it is unknotted and has self-linking number `-1`. -/
theorem hryniewicz_criterion (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H) (hdc : IsDynamicallyConvex H)
    (P : PeriodicOrbit H) (hP : P.IsPrime) :
    BoundsDiskLikeGlobalSection H P ↔ IsUnknotted H P ∧ HasSelfLinkingNumber H P (-1) := by sorry

end HryniewiczCriterion
