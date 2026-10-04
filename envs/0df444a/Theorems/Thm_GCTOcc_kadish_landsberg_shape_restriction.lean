-- Prove2me | Theorems.Thm_GCTOcc_kadish_landsberg_shape_restriction
-- name    : GCTOcc.kadish_landsberg_shape_restriction
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-14T17:35:30.715638+00:00
-- url     : https://prove2.me/theorems/27d1ee9d-5510-4322-bd58-35d725683228
-- title:
--   Theorem 2.1 (Kadish–Landsberg) — shape restrictions for $Z_{n,m}$
-- statement:
--   Let $\lambda \vdash nd$ occur in the degree $d$ part of the coordinate ring of the orbit closure $Z_{n,m}$ of the padded permanent. Then
--
--   $$\ell(\lambda) \le m^2 \qquad\text{and}\qquad |\bar\lambda| \le md,$$
--
--   where $\ell(\lambda)$ is the number of nonzero parts and $\bar\lambda$ is the **body** of $\lambda$, obtained by deleting the first part. The second condition is equivalent to $\lambda_1 \ge (n-m)d$: a partition occurring for the padded permanent must have a very long first row when $n$ is much larger than $m$.
--
--   This is the only property of $Z_{n,m}$ used in the proof of the main theorem, and it is what makes the main theorem possible: the partitions that could serve as occurrence obstructions are confined to a narrow family of shapes, and that family is then shown to occur for $\Omega_n$ as well. The source notes that the statement holds with $\mathrm{per}_m$ replaced by any homogeneous degree $m$ polynomial in $m^2$ variables, since only the padding is used.
--
--   **Formalization note.** $\lambda$ is a partition of $nd$ with at most $n^2$ parts; $\ell(\lambda)\le m^2$ is stated as "$\lambda_i = 0$ for all $i \ge m^2$", and $|\bar\lambda|$ as the sum of $\lambda_{i+1}$ over $i < n^2$, which covers all parts after the first.
-- source:
--   P. Bürgisser, C. Ikenmeyer, G. Panova, *No occurrence obstructions in geometric complexity theory*, J. Amer. Math. Soc. 32 (2019), 163–193, https://doi.org/10.1090/jams/908, p. 166, Theorem 2.1, attributed to H. Kadish and J. M. Landsberg, *Padded polynomials, their cousins, and geometric complexity theory*, Comm. Algebra 42 (2014), arXiv:1204.4772.

import Definitions.Def_GCTOcc_occurrence
open MvPolynomial

namespace GCTOcc

theorem kadish_landsberg_shape_restriction (n d m : ℕ) (lam : ℕ → ℕ)
    (hlam : IsPartitionOf lam (n * n) (n * d))
    (h : Occurs n d lam (orbitClosure n (paddedPerm m n))) :
    (∀ i, m * m ≤ i → lam i = 0) ∧ (∑ i ∈ Finset.range (n * n), lam (i + 1)) ≤ m * d := by sorry

end GCTOcc
