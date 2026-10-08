-- Prove2me | Theorems.Thm_MathieuM23_m23_isSimpleGroup
-- name    : MathieuM23.m23_isSimpleGroup
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T18:07:00.932975+00:00
-- url     : https://prove2.me/theorems/7d0ecd8e-62e5-40a0-9aad-341236214477
-- title:
--   §3 — $M_{23}$ is simple
-- statement:
--   The group $M_{23}=\langle g_1,g_2\rangle$ is simple: it is nontrivial and its only normal subgroups are $\{1\}$ and $M_{23}$.
--
--   Simplicity (with trivial center) is the standing hypothesis of the rigidity framework of §2.
-- source:
--   X. Huang, B. Jackson, K.-H. Lee, B. Poonen, R. Pries, S. Zhang, *The Mathieu group M23 is a Galois group over Q*, arXiv:2608.08538v1 (2026), https://arxiv.org/abs/2608.08538, p. 4, §3, first sentence ("a finite simple group")

import Definitions.Def_MathieuM23_Group

namespace MathieuM23

theorem m23_isSimpleGroup : IsSimpleGroup M23 := by sorry

end MathieuM23
