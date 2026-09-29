-- Prove2me | Theorems.Thm_GCT_mignon_ressayre_dc_lower_bound
-- name    : GCT.mignon_ressayre_dc_lower_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T16:15:53.531369+00:00
-- url     : https://prove2.me/theorems/b4f44e25-5c41-491a-9f5a-37f82a196e16
-- title:
--   Mignon–Ressayre: $\mathrm{dc}(\mathrm{perm}_m) \ge m^2/2$
-- statement:
--   **Mignon–Ressayre theorem.** If $n < m^2/2$ then there are no affine linear functions $x_{ij}(y)$, $1 \le i, j \le n$, with $\mathrm{perm}_m(Y) = \det_n(x(Y))$; that is, $$\mathrm{dc}(\mathrm{perm}_m) \;\ge\; \frac{m^2}{2}.$$ The proof compares the rank of the Hessian (second fundamental form) of the hypersurfaces $\{\det_n = 0\}$ and $\{\mathrm{perm}_m = 0\}$: at a smooth point of the determinant hypersurface that rank is at most $2n - 2$, at a suitable point of the permanent hypersurface it is the maximal $m^2 - 2$, and the rank cannot increase under an affine linear substitution. This is still the best known lower bound for the determinantal complexity of the permanent. Stated without division as $m^2 \le 2\,\mathrm{dc}(\mathrm{perm}_m)$.
-- source:
--   J. M. Landsberg, *Geometry and Complexity Theory*, Cambridge Studies in Advanced Mathematics 169, CUP 2017, DOI 10.1017/9781108183192, p. 172, Theorem 6.4.6.4 (Mignon–Ressayre [MR04]), stated also on p. 15 (§1.2.4); cf. J. M. Landsberg, *Geometric Complexity Theory: an introduction for geometers*, arXiv:1305.7387v3, https://arxiv.org/abs/1305.7387, p. 4, Theorem 2.3 and p. 11, Theorem 4.1. Original: T. Mignon and N. Ressayre, *A quadratic bound for the determinant and permanent problem*, IMRN 2004, no. 79, 4241–4253.

import Definitions.Def_GCT_determinantal_complexity

namespace GCT

theorem mignon_ressayre_dc_lower_bound (m : ℕ) : m ^ 2 ≤ 2 * dc m := by sorry

end GCT
