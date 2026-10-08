-- Prove2me | Theorems.Thm_MathieuM23_m23_four_transitive
-- name    : MathieuM23.m23_four_transitive
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T18:52:18.206158+00:00
-- url     : https://prove2.me/theorems/ea200cfb-0237-4a93-afed-f3e714458216
-- title:
--   §3 — $M_{23}$ is 4-transitive on 23 points
-- statement:
--   The natural action of $M_{23}$ on the $23$ points is $4$-transitive: for any two ordered $4$-tuples $(x_1,\dots,x_4)$ and $(y_1,\dots,y_4)$ of pairwise distinct points there is $\sigma\in M_{23}$ with $\sigma(x_i)=y_i$ for $i=1,\dots,4$.
-- source:
--   X. Huang, B. Jackson, K.-H. Lee, B. Poonen, R. Pries, S. Zhang, *The Mathieu group M23 is a Galois group over Q*, arXiv:2608.08538v1 (2026), https://arxiv.org/abs/2608.08538, p. 4, §3, second sentence

import Definitions.Def_MathieuM23_Group

namespace MathieuM23

theorem m23_four_transitive : MulAction.IsMultiplyPretransitive M23 (Fin 23) 4 := by sorry

end MathieuM23
