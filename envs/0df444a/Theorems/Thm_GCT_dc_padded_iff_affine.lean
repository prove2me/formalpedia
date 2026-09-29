-- Prove2me | Theorems.Thm_GCT_dc_padded_iff_affine
-- name    : GCT.dc_padded_iff_affine
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T16:13:48.277368+00:00
-- url     : https://prove2.me/theorems/4a8940e7-5bb9-4959-8e32-3d334e79e253
-- title:
--   Equation (1.2.4): padded orbit membership equals affine projection of $\det_n$
-- statement:
--   For all $m \le n$, the padded permanent $\ell^{\,n-m}\mathrm{perm}_m$ is the determinant of an $n \times n$ matrix of homogeneous linear forms in $(\ell, y_{11}, \dots, y_{mm})$ if and only if $\mathrm{perm}_m$ is an affine linear projection of $\det_n$, i.e. there are affine-linear functions $x_{ij}(y)$, $1 \le i, j \le n$, with $\mathrm{perm}_m(Y) = \det_n\big(x(Y)\big)$. This is the equivalence
--
--   $$\mathrm{dc}(\mathrm{perm}_m) \le n \iff \ell^{\,n-m}\mathrm{perm}_m \in \mathrm{End}(\mathbb{C}^{n^2}) \cdot \det_n$$
--
--   used throughout GCT to pass between Valiant's affine-projection definition of determinantal complexity and the homogeneous orbit picture inside $S^n W$; the passage is by homogenizing with $\ell$ in one direction and setting $\ell = 1$ in the other.
-- source:
--   J. M. Landsberg, *Geometry and Complexity Theory*, Cambridge Studies in Advanced Mathematics 169, CUP 2017, DOI 10.1017/9781108183192, p. 15, Equation (1.2.4), together with Definition 1.2.4.1 (dc as the smallest n for which p is an affine linear projection of the determinant); cf. J. M. Landsberg, *Geometric Complexity Theory: an introduction for geometers*, arXiv:1305.7387v3, https://arxiv.org/abs/1305.7387, p. 3, §2.1.

import Definitions.Def_GCT_determinantal_complexity

namespace GCT

theorem dc_padded_iff_affine (m n : ℕ) (hmn : m ≤ n) :
    HasLinearDetRep n (paddedPerm m n) ↔ HasAffineDetRep n (permPoly m) := by sorry

end GCT
