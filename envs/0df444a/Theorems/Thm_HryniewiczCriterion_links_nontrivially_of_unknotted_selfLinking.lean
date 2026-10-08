-- Prove2me | Theorems.Thm_HryniewiczCriterion_links_nontrivially_of_unknotted_selfLinking
-- name    : HryniewiczCriterion.links_nontrivially_of_unknotted_selfLinking
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-05T20:45:19.828259+00:00
-- url     : https://prove2.me/theorems/5193476e-7fd7-41b6-b0e0-a023ae10d43f
-- title:
--   Lemma 3.12: every other periodic orbit links the unknotted binding non-trivially
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped energy surface whose flow is dynamically convex. Let $\bar P$ be a prime periodic orbit that is unknotted with $\operatorname{sl}(\bar P)=-1$. Let $P$ be any periodic orbit on $S$, prime or not, that is geometrically different from $\bar P$, i.e. with a different image. Then
--   $$\operatorname{lk}(P,\bar P)\neq0.$$
--
--   This is the step that replaces the extra hypothesis of the non-degenerate criterion of Hryniewicz–Salomão, namely that $\bar P$ is linked to every orbit of index $2$.
-- source:
--   Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, https://arxiv.org/abs/1105.2077, Section 3.3, Lemma 3.12, p. 25 (under the standing assumptions of Section 3: dynamically convex, P-bar as in Theorem 1.7)

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

namespace HryniewiczCriterion

/-- Hryniewicz, Lemma 3.12: if `P̄` is a prime, unknotted periodic orbit with
`sl(P̄) = -1` of a dynamically convex flow, every periodic orbit geometrically different
from `P̄` links non-trivially with `P̄`. -/
theorem links_nontrivially_of_unknotted_selfLinking (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H) (hdc : IsDynamicallyConvex H)
    (P : PeriodicOrbit H) (hP : P.IsPrime)
    (hu : IsUnknotted H P) (hsl : HasSelfLinkingNumber H P (-1))
    (Q : PeriodicOrbit H) (hQ : Q.image ≠ P.image) :
    LinksNontrivially P Q := by sorry

end HryniewiczCriterion
