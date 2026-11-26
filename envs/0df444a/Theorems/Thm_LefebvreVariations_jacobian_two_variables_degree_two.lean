-- Prove2me | Theorems.Thm_LefebvreVariations_jacobian_two_variables_degree_two
-- name    : LefebvreVariations.jacobian_two_variables_degree_two
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:11:46.197501+00:00
-- url     : https://prove2.me/theorems/55880a4b-8fa0-4d09-a9ee-5a9481460582
-- title:
--   Lefebvre's variations, No. 139 — on a theme by Wang: the Jacobian conjecture in two variables holds for maps of degree at most two
-- statement:
--   Let $F=(F_1,F_2)$ be polynomials in $\mathbb{C}[x_1,x_2]$ of total degree at most $2$ whose Jacobian determinant $\det(\partial F_i/\partial x_j)$ is a unit of $\mathbb{C}[x_1,x_2]$ (a non-zero constant). Then there is $G=(G_1,G_2)$ with $G_i(F_1,F_2)=x_i$ and $F_i(G_1,G_2)=x_i$ for $i=1,2$.
--
--   This is the two-variable Jacobian conjecture restricted to quadratic maps; it is a special case of S. S.-S. Wang's theorem (1980) that the Jacobian conjecture holds for maps of degree at most 2 in any number of variables. The platform problem `FCP.Jacobian.jacobian_two_variables` is the unrestricted statement.
--
--   **Formalization Note** `hdeg` bounds `MvPolynomial.totalDegree` of each component by 2. The Jacobian matrix is `Matrix.of fun i j => pderiv j (F i)` and `IsUnit` of its determinant is taken in `MvPolynomial (Fin 2) ℂ`. The conclusion follows the parent: `aeval F (G i) = X i` (composition `G ∘ F` is the identity) and `aeval G (F i) = X i` (`F ∘ G` is the identity).
--
--   **Why this is a variation.** Variation on the open FCP.Jacobian.jacobian_two_variables (Jacobian conjecture, n = 2). It adds the hypothesis that both components have total degree at most 2 and takes k = C; the conclusion is the parent's JacobianConjectureProp written out. It is a partial result (Wang 1980) and a first elementary slice for attacking the parent.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   S. S.-S. Wang, A Jacobian criterion for separability, J. Algebra 65 (1980) 453-494: the Jacobian conjecture holds for polynomial maps of degree at most 2 over a field of characteristic 0, in all dimensions (title, journal, volume, pages and the degree-2 statement verified by web search). Origin: platform theorem FCP.Jacobian.jacobian_two_variables (Open), restricted to total degree <= 2.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

open MvPolynomial

/-- The two-variable Jacobian conjecture over `ℂ` for maps of total degree at most 2 (Wang's theorem),
with the parent's `JacobianConjectureProp ℂ 2` written out: `comp G F = id` is `aeval F (G i) = X i`
and `comp F G = id` is `aeval G (F i) = X i`. -/
theorem jacobian_two_variables_degree_two
    (F : Fin 2 → MvPolynomial (Fin 2) ℂ) (hdeg : ∀ i, (F i).totalDegree ≤ 2)
    (hF : IsUnit (Matrix.of fun i j => pderiv j (F i)).det) :
    ∃ G : Fin 2 → MvPolynomial (Fin 2) ℂ,
      (∀ i, aeval F (G i) = X i) ∧ (∀ i, aeval G (F i) = X i) := by
  sorry

end LefebvreVariations
