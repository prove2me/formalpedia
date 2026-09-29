-- Prove2me | Theorems.Thm_GCT_dc_le_two_pow_sub_one
-- name    : GCT.dc_le_two_pow_sub_one
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T16:15:12.303872+00:00
-- url     : https://prove2.me/theorems/30fab5bf-1522-4fc2-b8ae-3ce0f99c19da
-- title:
--   Grenet's upper bound $\mathrm{dc}(\mathrm{perm}_m) \le 2^m - 1$
-- statement:
--   **Grenet's upper bound.** The permanent of an $m \times m$ matrix is an affine linear projection of the determinant of size $2^m - 1$; equivalently $\mathrm{dc}(\mathrm{perm}_m) \le 2^m - 1$. Grenet's construction indexes rows and columns by proper subsets of $\{1, \dots, m\}$ and realizes the expansion of the permanent as a determinant of that size; it improves Valiant's earlier bound $4^m$ and remains the best known upper bound. For $m = 3$ it gives the size-$7$ expression, which is optimal.
-- source:
--   J. M. Landsberg, *Geometry and Complexity Theory*, Cambridge Studies in Advanced Mathematics 169, CUP 2017, DOI 10.1017/9781108183192, p. 14 (§1.2.4) and §6.6.3, p. 178 ('The best known determinantal expression of perm_m is of size 2^m - 1 and is due to Grenet [Gre11]'); B. Grenet, *An upper bound for the permanent versus determinant problem*, 2011.

import Definitions.Def_GCT_determinantal_complexity

namespace GCT

theorem dc_le_two_pow_sub_one (m : ℕ) : dc m ≤ 2 ^ m - 1 := by sorry

end GCT
