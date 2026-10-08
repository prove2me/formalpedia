-- Prove2me | Theorems.Thm_MathieuM23_nielsenClass_ncard
-- name    : MathieuM23.nielsenClass_ncard
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T21:59:45.714974+00:00
-- url     : https://prove2.me/theorems/0cebe506-3819-4a37-a6d7-278460e64007
-- title:
--   §3 — $|\mathrm{Ni}_c|=7$ for $c=(2,23A,23B)$
-- statement:
--   For the classes $C_1=2$, $C_2=23A$, $C_3=23B$ of $M_{23}$ (the classes of $g_1,g_2,g_3$), the Nielsen class
--
--   $$\mathrm{Ni}_c=M_{23}\backslash\{(h_1,h_2,h_3)\in C_1\times C_2\times C_3: h_1h_2h_3=1,\ \langle h_1,h_2,h_3\rangle=M_{23}\}$$
--
--   has exactly $7$ elements:
--
--   $$|\mathrm{Ni}_c|=7.$$
--
--   Hence, by the Riemann existence theorem, there are exactly seven $M_{23}$-covers of $\mathbb{P}^1_{\mathbb{C}}$ with this ramification data. The triple is therefore not rigid, and this is the starting point of the paper's construction.
-- source:
--   X. Huang, B. Jackson, K.-H. Lee, B. Poonen, R. Pries, S. Zhang, *The Mathieu group M23 is a Galois group over Q*, arXiv:2608.08538v1 (2026), https://arxiv.org/abs/2608.08538, p. 4, §3 ("This is $\{2, 23A, 23B\}$, with $|\mathrm{Ni}_c| = 7$")

import Definitions.Def_MathieuM23_Nielsen

namespace MathieuM23

theorem nielsenClass_ncard : nielsenClass.ncard = 7 := by sorry

end MathieuM23
