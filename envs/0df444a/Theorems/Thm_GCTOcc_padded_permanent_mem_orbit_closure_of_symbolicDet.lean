-- Prove2me | Theorems.Thm_GCTOcc_padded_permanent_mem_orbit_closure_of_symbolicDet
-- name    : GCTOcc.padded_permanent_mem_orbit_closure_of_symbolicDet
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T17:12:42.146264+00:00
-- url     : https://prove2.me/theorems/105856a3-ca68-40f1-85a2-7cdd9e0c3518
-- title:
--   A symbolic determinant of size $n$ puts $X_{00}^{n-m}\mathrm{per}_m$ into $\Omega_n$
-- statement:
--   Let $m \le n$. If the permanent $\mathrm{per}_m$ is the determinant of an $n \times n$ matrix whose entries are affine linear polynomials — that is, if the determinantal complexity of $\mathrm{per}_m$ is at most $n$ — then the padded permanent lies in the orbit closure of the determinant:
--
--   $$X_{00}^{\,n-m}\,\mathrm{per}_m \;\in\; \Omega_n \;=\; \overline{\mathrm{GL}_{n^2}\cdot \det\nolimits_n}.$$
--
--   This is the bridge between Valiant's affine formulation of determinantal complexity and the homogeneous orbit-closure formulation used throughout geometric complexity theory: it is the reason why a lower bound obtained by separating orbit closures is a lower bound on determinantal complexity. The proof in the source homogenizes the affine substitution and uses that the invertible matrices are dense among all matrices, so a determinant of linear forms obtained from a possibly singular substitution is still a limit of points of the orbit.
--
--   **Formalization note.** The hypothesis is stated as the existence of an $n \times n$ matrix of polynomials of total degree at most one whose determinant is $\mathrm{per}_m$; membership in $\Omega_n$ is coefficientwise convergence of a sequence of orbit points.
-- source:
--   P. Bürgisser, C. Ikenmeyer, G. Panova, *No occurrence obstructions in geometric complexity theory*, J. Amer. Math. Soc. 32 (2019), 163–193, https://doi.org/10.1090/jams/908, p. 164, §1(a), the paragraph after Conjecture 1.2: '$\mathrm{dc}(\mathrm{per}_m) \le n$ implies $X_{11}^{n-m}\mathrm{per}_m \in \Omega_n$', which is why Conjecture 1.2 implies Conjecture 1.1 (Valiant).

import Definitions.Def_GCTOcc_occurrence
open MvPolynomial

namespace GCTOcc

theorem padded_permanent_mem_orbit_closure_of_symbolicDet (m n : ℕ) (hmn : m ≤ n)
    (h : IsSymbolicDet (permPoly m) n) :
    paddedPerm m n ∈ orbitClosure n (detPoly n) := by sorry

end GCTOcc
