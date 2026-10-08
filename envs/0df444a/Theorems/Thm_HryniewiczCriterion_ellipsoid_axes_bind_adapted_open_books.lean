-- Prove2me | Theorems.Thm_HryniewiczCriterion_ellipsoid_axes_bind_adapted_open_books
-- name    : HryniewiczCriterion.ellipsoid_axes_bind_adapted_open_books
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T20:07:28.803787+00:00
-- url     : https://prove2.me/theorems/c7326d94-860b-4fd6-a75f-be7a102e582a
-- title:
--   Ellipsoids: both axes bind adapted open books with disk-like pages
-- statement:
--   Let $r_1,r_2>0$ and let $S$ be the boundary of the ellipsoid
--   $$\frac{q_1^2+p_1^2}{r_1^2}+\frac{q_2^2+p_2^2}{r_2^2}=1.$$
--   Let $P$ be a prime periodic orbit of $X_H$ on $S$, with $H$ the left-hand side, whose image lies in one of the two axes $\{q_2=p_2=0\}$ or $\{q_1=p_1=0\}$. Then $P$ is the binding of an open book decomposition of $S$ with disk-like pages that is adapted to the flow: every page is a disk-like global surface of section with oriented boundary $P$.
--
--   Hryniewicz notes that the axes of an ellipsoid are bindings of adapted open books, while the Hofer–Wysocki–Zehnder theorem detects only the axis of smaller action. The statement is an explicit example of the notions used in Theorems 1.7 and 1.8. It checks that the definitions of global sections and open books are satisfiable.
-- source:
--   Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, https://arxiv.org/abs/1105.2077, p. 3, paragraph after Theorem 1.7

import Definitions.Def_HryniewiczCriterion_GlobalSection

namespace HryniewiczCriterion

/-- Hryniewicz, p. 3: on the boundary of an ellipsoid, each of the two axis circles is
the binding of an adapted open book decomposition with disk-like pages. -/
theorem ellipsoid_axes_bind_adapted_open_books (r₁ r₂ : ℝ) (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (P : PeriodicOrbit
      (fun x : R4 => (x 0 ^ 2 + x 1 ^ 2) / r₁ ^ 2 + (x 2 ^ 2 + x 3 ^ 2) / r₂ ^ 2))
    (hP : P.IsPrime)
    (haxis : P.image ⊆ {x | x 2 = 0 ∧ x 3 = 0} ∨ P.image ⊆ {x | x 0 = 0 ∧ x 1 = 0}) :
    HasAdaptedDiskOpenBook
      (fun x : R4 => (x 0 ^ 2 + x 1 ^ 2) / r₁ ^ 2 + (x 2 ^ 2 + x 3 ^ 2) / r₂ ^ 2) P := by sorry

end HryniewiczCriterion
