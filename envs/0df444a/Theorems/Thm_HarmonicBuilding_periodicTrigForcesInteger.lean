-- Prove2me | Theorems.Thm_HarmonicBuilding_periodicTrigForcesInteger
-- name    : HarmonicBuilding.periodicTrigForcesInteger
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T12:48:04.891683+00:00
-- url     : https://prove2.me/theorems/516f4102-65eb-4d53-9670-d8ddde5cd321
-- title:
--   A $2\pi$-periodic $A\cos(a\theta)+B\sin(a\theta)$ is zero or has $a \in \mathbb{Z}$
-- statement:
--   Let $a,A,B$ be real numbers and suppose the function
--
--   $$
--   f(\theta)=A\cos(a\theta)+B\sin(a\theta)
--   $$
--
--   is $2\pi$-periodic. Then either both coefficients vanish, so that $f$ is identically zero, or $a$ is an integer.
--
--   The statement is elementary but it is the step that produces discreteness in the order theorem. Writing $c=2\pi a$ and expanding the addition formulas, periodicity says that the vector $(A,B)$ is fixed by the plane rotation through angle $c$:
--
--   $$
--   A(\cos c-1)+B\sin c=0,\qquad -A\sin c+B(\cos c-1)=0 .
--   $$
--
--   The determinant of this system is $(\cos c-1)^2+\sin^2 c=2-2\cos c$. If $\cos c\ne1$ the system is nondegenerate and forces $A=B=0$. If $\cos c=1$ then $c\in 2\pi\mathbb{Z}$, and dividing by $2\pi$ gives $a\in\mathbb{Z}$.
--
--   In the setting of harmonic maps into buildings this is applied with $a=2\alpha$ to the oscillating part of the squared distance from the image of the unit circle to the cone point. That function is automatically $2\pi$-periodic, being a function on the circle, so the alternative reads: either the distance is constant, or $2\alpha$ is an integer. Those are exactly the two branches of the dichotomy.
-- source:
--   Christine Breiner and Ben K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calculus of Variations and Partial Differential Equations (2026), arXiv:2604.16608, https://doi.org/10.1007/s00526-026-03375-5, proof of Theorem 3.1 (Section 3), step 5: since q extends smoothly to all of S^1, unless both coefficients vanish 2*alpha must be an integer. Stated here as the underlying elementary fact about 2*pi-periodic sinusoids, with no reference to buildings.

import Mathlib

namespace HarmonicBuilding

theorem periodicTrigForcesInteger (a A B : ℝ)
    (hper : ∀ theta : ℝ,
      A * Real.cos (a * (theta + 2 * Real.pi))
          + B * Real.sin (a * (theta + 2 * Real.pi))
        = A * Real.cos (a * theta) + B * Real.sin (a * theta)) :
    (A = 0 ∧ B = 0) ∨ ∃ n : ℤ, a = (n : ℝ) := by sorry

end HarmonicBuilding
