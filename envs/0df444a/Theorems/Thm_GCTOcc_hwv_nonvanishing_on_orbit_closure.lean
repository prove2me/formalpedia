-- Prove2me | Theorems.Thm_GCTOcc_hwv_nonvanishing_on_orbit_closure
-- name    : GCTOcc.hwv_nonvanishing_on_orbit_closure
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T17:46:12.368025+00:00
-- url     : https://prove2.me/theorems/9df98c42-873a-49b0-991c-d128c855fbe8
-- title:
--   Proposition 2.4 — highest weight vectors with a long first row do not vanish on $\Omega_n$
-- statement:
--   Let $\lambda \vdash nd$ and suppose there is a positive integer $m$ with
--
--   $$|\bar\lambda| \le md \qquad\text{and}\qquad md^2 \le n,$$
--
--   where $\bar\lambda$ is $\lambda$ with its first part deleted. Then every highest weight vector of weight $\lambda$ in $\mathrm{Sym}^d\mathrm{Sym}^n V$, viewed as a degree $d$ polynomial function on the space of forms, fails to vanish identically on $\Omega_n$. In particular, if $\lambda$ occurs in the plethysm $\mathrm{Sym}^d \mathrm{Sym}^n V$ at all, then $\lambda$ occurs in $\mathbb{C}[\Omega_n]_d$.
--
--   This is the small-degree half of the proof of the main theorem: when $d$ is small compared with $m$, no combinatorial decomposition into rectangles is available, and instead one shows that the restriction map from the coordinate ring of the ambient space to that of $\Omega_n$ is injective on the whole $\lambda$-isotypic component. The proof goes through an explicit lifting map for highest weight vectors in plethysms and a contraction rule for the generators labelled by tableaux.
--
--   **Formalization note.** "Highest weight vector in $\mathrm{Sym}^d\mathrm{Sym}^n V$" is rendered as a degree $d$ Borel eigenvector of weight $\lambda$ on the space of degree $n$ forms; "does not vanish identically" is the hypothesis that it is nonzero at some form, and the conclusion is that it is nonzero at some point of $\Omega_n$.
-- source:
--   P. Bürgisser, C. Ikenmeyer, G. Panova, *No occurrence obstructions in geometric complexity theory*, J. Amer. Math. Soc. 32 (2019), 163–193, https://doi.org/10.1090/jams/908, p. 167, Proposition 2.4.

import Definitions.Def_GCTOcc_occurrence
open MvPolynomial

namespace GCTOcc

theorem hwv_nonvanishing_on_orbit_closure (n d m : ℕ) (lam : ℕ → ℕ)
    (hlam : IsPartitionOf lam (n * n) (n * d))
    (hbody : (∑ i ∈ Finset.range (n * n), lam (i + 1)) ≤ m * d) (hmd : m * d ^ 2 ≤ n)
    (F : CoordRing) (hF : IsHWV n d lam F) (hF0 : ∃ q : PolyR, IsForm n q ∧ evalCoeff q F ≠ 0) :
    ∃ p ∈ orbitClosure n (detPoly n), evalCoeff p F ≠ 0 := by sorry

end GCTOcc
