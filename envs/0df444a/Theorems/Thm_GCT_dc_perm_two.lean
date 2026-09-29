-- Prove2me | Theorems.Thm_GCT_dc_perm_two
-- name    : GCT.dc_perm_two
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T16:18:32.862711+00:00
-- url     : https://prove2.me/theorems/ca459660-c109-4042-91ca-4e5bf93a82d9
-- title:
--   $\mathrm{dc}(\mathrm{perm}_2) = \overline{\mathrm{dc}}(\mathrm{perm}_2) = 2$
-- statement:
--   The base case $m = 2$: both the determinantal and the border determinantal complexity of $\mathrm{perm}_2 = y_{11}y_{22} + y_{12}y_{21}$ equal $2$. The upper bound is the identity $$y_{11}y_{22} + y_{12}y_{21} = \det \begin{pmatrix} y_{11} & -y_{12} \\ y_{21} & y_{22}\end{pmatrix},$$ and the lower bound holds because a polynomial of degree $2$ is neither the determinant of a $1 \times 1$ matrix of linear forms nor a limit of such.
-- source:
--   J. M. Landsberg, *Geometric Complexity Theory: an introduction for geometers*, arXiv:1305.7387v3, https://arxiv.org/abs/1305.7387, p. 4, §2.1 ('For example, dc-bar(perm_2) = 2').

import Definitions.Def_GCT_determinantal_complexity

namespace GCT

theorem dc_perm_two : dc 2 = 2 ∧ dcBar 2 = 2 := by sorry

end GCT
