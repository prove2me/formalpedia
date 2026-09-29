-- Prove2me | Theorems.Thm_GCTOcc_orbit_closure_det_two_eq_forms
-- name    : GCTOcc.orbit_closure_det_two_eq_forms
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T17:13:38.338836+00:00
-- url     : https://prove2.me/theorems/a895c4a2-3041-4cbe-87e9-3aa2da5c19e3
-- title:
--   $\Omega_2 = \mathrm{Sym}^2(\mathbb{C}^{2\times 2})^*$
-- statement:
--   For $n = 2$ the orbit closure of the determinant is the whole space of forms: every quadratic form $p$ in the four variables $X_{00}, X_{01}, X_{10}, X_{11}$ lies in
--
--   $$\Omega_2 = \overline{\mathrm{GL}_4 \cdot \det\nolimits_2}, \qquad \det\nolimits_2 = X_{00}X_{11} - X_{01}X_{10}.$$
--
--   The reason is that $\det_2$ is a nondegenerate quadratic form in four variables, every quadratic form of rank at most $4$ is a linear substitution of it, and the forms of rank exactly $4$ are dense. The statement is the smallest nontrivial case of the orbit closure $\Omega_n$ and serves as a sanity anchor for the definitions: it shows the orbit closure is genuinely large and that the coefficientwise limit definition has the intended content.
--
--   **Formalization note.** "Quadratic form in the four variables" is rendered as: $p$ is homogeneous of degree $2$ and every variable occurring in $p$ has both indices smaller than $2$. Only the inclusion $\mathrm{Sym}^2(\mathbb{C}^{2\times2})^* \subseteq \Omega_2$ is asserted, the reverse inclusion being immediate from the definition of the orbit closure.
-- source:
--   P. Bürgisser, C. Ikenmeyer, G. Panova, *No occurrence obstructions in geometric complexity theory*, J. Amer. Math. Soc. 32 (2019), 163–193, https://doi.org/10.1090/jams/908, p. 164, §1(a): 'It is easy to see that $\Omega_2 = \mathrm{Sym}^2(\mathbb{C}^{2\times 2})^*$.'

import Definitions.Def_GCTOcc_occurrence
open MvPolynomial

namespace GCTOcc

theorem orbit_closure_det_two_eq_forms (p : PolyR) (hp : IsForm 2 p) :
    p ∈ orbitClosure 2 (detPoly 2) := by sorry

end GCTOcc
