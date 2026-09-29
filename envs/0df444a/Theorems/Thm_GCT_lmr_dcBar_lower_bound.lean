-- Prove2me | Theorems.Thm_GCT_lmr_dcBar_lower_bound
-- name    : GCT.lmr_dcBar_lower_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T16:17:07.664955+00:00
-- url     : https://prove2.me/theorems/50155aa7-ef1e-43b8-a814-1d30d3314645
-- title:
--   Landsberg–Manivel–Ressayre: $\overline{\mathrm{dc}}(\mathrm{perm}_m) \ge m^2/2$
-- statement:
--   **Landsberg–Manivel–Ressayre theorem.** The border determinantal complexity of the permanent satisfies $$\overline{\mathrm{dc}}(\mathrm{perm}_m) \;\ge\; \frac{m^2}{2},$$ i.e. $\mathrm{Perm}^m_n \not\subseteq \mathrm{Det}_n$ whenever $n < m^2/2$. The proof goes through the varieties $\mathrm{Dual}_{k,d,N}$ of degree-$d$ hypersurfaces in $\mathbb{P}^{N-1}$ whose dual variety has dimension at most $k$: these admit an explicit $GL_N$-module of set-theoretic equations, $\mathrm{Det}_n$ is contained in $\mathrm{Dual}_{2n-2,n,n^2}$, and the dual variety of $\{\mathrm{perm}_m = 0\}$ is a hypersurface, a property that survives padding by $\ell^{\,n-m}$. Unlike the Mignon–Ressayre bound, this one applies to the orbit closure, hence directly to the flagship conjecture. Stated without division as $m^2 \le 2\,\overline{\mathrm{dc}}(\mathrm{perm}_m)$.
-- source:
--   J. M. Landsberg, *Geometric Complexity Theory: an introduction for geometers*, arXiv:1305.7387v3, https://arxiv.org/abs/1305.7387, p. 4, Theorem 2.2, with the proof discussed on p. 12, §4.2; original: J. M. Landsberg, L. Manivel and N. Ressayre, *Hypersurfaces with degenerate duals and the geometric complexity theory program*, Comment. Math. Helv. 88 (2013), 469–484.

import Definitions.Def_GCT_determinantal_complexity

namespace GCT

theorem lmr_dcBar_lower_bound (m : ℕ) : m ^ 2 ≤ 2 * dcBar m := by sorry

end GCT
