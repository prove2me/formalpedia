-- Prove2me | Theorems.Thm_HryniewiczCriterion_adapted_open_book_of_unknotted_selfLinking
-- name    : HryniewiczCriterion.adapted_open_book_of_unknotted_selfLinking
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-05T21:01:04.705523+00:00
-- url     : https://prove2.me/theorems/a6e13bc6-a738-4afa-bc90-302ed0984e3f
-- title:
--   Theorem 1.7 (open book): an unknotted orbit with $\operatorname{sl}=-1$ binds an adapted open book
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped energy surface whose flow is dynamically convex. Let $\bar P$ be a prime periodic orbit that is unknotted with $\operatorname{sl}(\bar P)=-1$. Then $\bar P$ is the binding of an open book decomposition of $S$ with disk-like pages, adapted to the flow: every page is a disk-like global surface of section whose oriented boundary is $\bar P$.
--
--   This strengthens the "if" direction of Hryniewicz's criterion from a single disk to a whole family of disk-like global sections that fill $S\setminus\bar P$.
-- source:
--   Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, https://arxiv.org/abs/1105.2077, Theorem 1.7, p. 3, second sentence

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

namespace HryniewiczCriterion

/-- Hryniewicz, Theorem 1.7, second sentence: a prime, unknotted periodic orbit with
`sl = -1` of a dynamically convex flow is the binding of an adapted open book
decomposition with disk-like pages. -/
theorem adapted_open_book_of_unknotted_selfLinking (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H) (hdc : IsDynamicallyConvex H)
    (P : PeriodicOrbit H) (hP : P.IsPrime)
    (hu : IsUnknotted H P) (hsl : HasSelfLinkingNumber H P (-1)) :
    HasAdaptedDiskOpenBook H P := by sorry

end HryniewiczCriterion
