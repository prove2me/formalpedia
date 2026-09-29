-- Prove2me | Theorems.Thm_GCT_abv_dc_perm_three_four
-- name    : GCT.abv_dc_perm_three_four
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T16:24:39.479282+00:00
-- url     : https://prove2.me/theorems/f39add4e-f5d0-4aaa-b17e-ab090aa15530
-- title:
--   Alper–Bogart–Velasco: $\mathrm{dc}(\mathrm{perm}_3) = 7$ and $\mathrm{dc}(\mathrm{perm}_4) \ge 9$
-- statement:
--   **Alper–Bogart–Velasco.** The determinantal complexity of the $3 \times 3$ permanent is exactly $7$, and that of the $4 \times 4$ permanent is at least $9$. The upper bound $\mathrm{dc}(\mathrm{perm}_3) \le 7$ is Grenet's size-$2^3 - 1 = 7$ expression. The lower bounds follow from a bound of the shape $\mathrm{dc}(P) \ge \mathrm{codim}\,\mathrm{Sing}(Z(P)) + 1$, obtained by taking one derivative, together with the computation $\mathrm{codim}\big(\mathrm{Sing}\{\mathrm{perm}_m = 0\}\big) = 2m$ for $m = 3, 4$. These are the only cases where the determinantal complexity of the permanent is known exactly, or beyond the general quadratic bound.
-- source:
--   J. M. Landsberg, *Geometry and Complexity Theory*, Cambridge Studies in Advanced Mathematics 169, CUP 2017, DOI 10.1017/9781108183192, p. 163, Corollary 6.3.4.8 ([ABV15]: 'dc(perm_3) = 7 and dc(perm_4) ≥ 9'), the upper bound being (1.2.3); original: J. Alper, T. Bogart and M. Velasco, *A lower bound for the determinantal complexity of a hypersurface*, Found. Comput. Math. 17 (2017), 829–836.

import Definitions.Def_GCT_determinantal_complexity

namespace GCT

theorem abv_dc_perm_three_four : dc 3 = 7 ∧ 9 ≤ dc 4 := by sorry

end GCT
