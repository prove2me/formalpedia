-- Prove2me | Theorems.Thm_MathieuM23_m23_card
-- name    : MathieuM23.m23_card
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T17:36:52.229303+00:00
-- url     : https://prove2.me/theorems/41f315fe-d0ca-4c6b-8424-d8384a7cae85
-- title:
--   §3 — $|M_{23}|=10{,}200{,}960$
-- statement:
--   The Mathieu group $M_{23}=\langle g_1,g_2\rangle\le S_{23}$ has order
--
--   $$|M_{23}|=10{,}200{,}960=2^7\cdot3^2\cdot5\cdot7\cdot11\cdot23.$$
--
--   This pins down that the explicit generators $g_1,g_2$ really generate the Mathieu group, and not a smaller or larger subgroup of $S_{23}$.
-- source:
--   X. Huang, B. Jackson, K.-H. Lee, B. Poonen, R. Pries, S. Zhang, *The Mathieu group M23 is a Galois group over Q*, arXiv:2608.08538v1 (2026), https://arxiv.org/abs/2608.08538, p. 4, §3, first sentence

import Definitions.Def_MathieuM23_Group

namespace MathieuM23

theorem m23_card : Nat.card M23 = 10200960 := by sorry

end MathieuM23
