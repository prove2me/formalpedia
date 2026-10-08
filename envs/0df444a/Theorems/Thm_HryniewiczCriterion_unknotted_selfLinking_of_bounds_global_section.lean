-- Prove2me | Theorems.Thm_HryniewiczCriterion_unknotted_selfLinking_of_bounds_global_section
-- name    : HryniewiczCriterion.unknotted_selfLinking_of_bounds_global_section
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T20:27:26.853258+00:00
-- url     : https://prove2.me/theorems/0dd5488e-9c21-4330-9a59-84c13106a63e
-- title:
--   Theorem 1.7 (necessity): a binding of a disk-like global section is unknotted with $\operatorname{sl}=-1$
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped energy surface whose flow is dynamically convex. Let $\bar P$ be a prime periodic orbit on $S$. If $\bar P$ bounds a disk-like global surface of section, then
--   $$\bar P\ \text{is unknotted}\quad\text{and}\quad \operatorname{sl}(\bar P)=-1.$$
--
--   This is the "only if" half of Hryniewicz's criterion. Unknottedness is immediate from the spanning disk. The value of the self-linking number comes from the transversality of the disk to the flow.
-- source:
--   Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, https://arxiv.org/abs/1105.2077, Theorem 1.7, p. 3 (only-if direction; proof outline p. 4, via Proposition 2.1 of Hryniewicz, Trans. AMS 364 (2012), https://arxiv.org/abs/0812.4076)

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

namespace HryniewiczCriterion

/-- Hryniewicz, Theorem 1.7, "only if" direction: a prime periodic orbit of a
dynamically convex flow that bounds a disk-like global surface of section is unknotted
and has self-linking number `-1`. -/
theorem unknotted_selfLinking_of_bounds_global_section (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H) (hdc : IsDynamicallyConvex H)
    (P : PeriodicOrbit H) (hP : P.IsPrime)
    (hD : BoundsDiskLikeGlobalSection H P) :
    IsUnknotted H P ∧ HasSelfLinkingNumber H P (-1) := by sorry

end HryniewiczCriterion
