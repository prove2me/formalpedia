-- Prove2me | Theorems.Thm_GCT_dcBar_le_dc
-- name    : GCT.dcBar_le_dc
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T16:16:19.294796+00:00
-- url     : https://prove2.me/theorems/9a9ee9ec-56f6-4b22-920e-f7d1f3b33a13
-- title:
--   Border determinantal complexity is at most determinantal complexity
-- statement:
--   Since $\mathrm{End}(\mathbb{C}^{n^2}) \cdot \det_n$ is contained in its own closure $\overline{\mathrm{End}(\mathbb{C}^{n^2}) \cdot \det_n} = \mathrm{Det}_n$, every determinantal expression is in particular a border expression, so $$\overline{\mathrm{dc}}(\mathrm{perm}_m) \;\le\; \mathrm{dc}(\mathrm{perm}_m)$$ for all $m$. This inequality is what makes the GCT flagship conjecture a strengthening of Valiant's conjecture, and it is what transfers a lower bound for $\overline{\mathrm{dc}}$ to one for $\mathrm{dc}$.
-- source:
--   J. M. Landsberg, *Geometric Complexity Theory: an introduction for geometers*, arXiv:1305.7387v3, https://arxiv.org/abs/1305.7387, p. 4, §2.1 ('Define dc(P) to be the smallest n such that l^(n-m) P ∈ End(W)·det_n, so dc-bar(P) ≤ dc(P)'); cf. J. M. Landsberg, *Geometry and Complexity Theory*, Cambridge Studies in Advanced Mathematics 169, CUP 2017, DOI 10.1017/9781108183192, p. 16, Definition 1.2.5.1.

import Definitions.Def_GCT_determinantal_complexity

namespace GCT

theorem dcBar_le_dc (m : ℕ) : dcBar m ≤ dc m := by sorry

end GCT
