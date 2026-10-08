-- Prove2me | Theorems.Thm_HryniewiczCriterion_linksNontrivially_of_isDiskLikeGlobalSectionMap
-- name    : HryniewiczCriterion.linksNontrivially_of_isDiskLikeGlobalSectionMap
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-08T09:48:30.936133+00:00
-- url     : https://prove2.me/theorems/1f8b271a-b6b6-4b0f-96e1-e0512ca284f6
-- title:
--   A periodic orbit that bounds a disk-like global surface of section links every other periodic orbit non-trivially
-- statement:
--   Let $S=H^{-1}(1)$ be a strictly star-shaped level, and let $P=(x_P,T_P)$ be a periodic orbit (not necessarily prime) that bounds a disk-like global surface of section $D=e(\overline{\mathbb D})$ with $\partial D=e(S^1)=x_P(\mathbb{R})$. Let $Q=(x_Q,T_Q)$ be any periodic orbit on $S$ with $x_Q(\mathbb{R})\neq x_P(\mathbb{R})$. Then the loops $s\mapsto x_P(T_Ps)/|x_P(T_Ps)|$ and $s\mapsto x_Q(T_Qs)/|x_Q(T_Qs)|$ in $S^3$ have a linking number $n$ in the Gauss-integral sense of `IsLinkingNumber`, and $n\neq0$.
--
--   Proof idea. By uniqueness of trajectories the two images are disjoint. So $Q$ misses $\partial D$, and $Q\cap D$ is a compact subset of the interior. There $X_H$ is transverse to $D$, so the intersections are isolated and finite in number. Since $D\setminus\partial D$ is connected and $X_H$ never lies in its tangent plane, $X_H$ crosses $D$ from the same side at every point, so all intersections have the same sign. The global-section property forces at least one intersection. The linking number equals the algebraic intersection number of the loop $Q$ (traversed over $[0,T_Q]$) with the Seifert surface $D$ of $P$, which is therefore $\pm\#(Q\cap D)\neq0$, counted with the multiplicity of the covers.
-- source:
--   Standard (linking number = algebraic intersection number with a Seifert surface; Rolfsen, Knots and Links, 1976, Ch. 5D); used in U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, arXiv:1105.2077, proof of Lemma 3.12 (p. 26) and Definition 1.2.

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion

theorem HryniewiczCriterion.linksNontrivially_of_isDiskLikeGlobalSectionMap (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (P Q : PeriodicOrbit H)
    (e : Plane → R4) (he : IsDiskLikeGlobalSectionMap H P e) (hQ : Q.image ≠ P.image) :
    LinksNontrivially P Q := by sorry
