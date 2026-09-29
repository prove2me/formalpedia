-- Prove2me | Theorems.Thm_OPG401_root_problem
-- name    : OPG401.root_problem
-- status  : Open
-- author  : @hao jia
-- created : 2026-09-07T07:14:07.56368+00:00
-- url     : https://prove2.me/theorems/50f0bfcf-b84f-4f7e-952f-2e2ed50c6fd8
-- title:
--   OPG-401: circular chromatic number at most 20/7
-- statement:
--   Let $G$ be any finite simple graph that is planar, triangle-free, and has maximum degree at most three. Then there exists a map $\varphi:V(G)\to\mathbb Z_{20}$ such that every edge has cyclic color distance between $7$ and $13$:
--
--   $$
--   7\le d_{20}(\varphi(u),\varphi(v))\le13
--   \qquad\text{for every }uv\in E(G).
--   $$
--
--   Equivalently, every graph in the stated class has circular chromatic number at most $20/7$. Disconnected and empty graphs are included.
-- source:
--   Open Problem Garden / UnsolvedMath OPG-401, https://www.unsolvedmath.com/problems/OPG-401

import Definitions.Def_opg401_circular_coloring

namespace OPG401

universe u

/-- OPG-401: every finite simple triangle-free planar subcubic graph has a
`(20,7)`-coloring. -/
theorem root_problem
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hplanar : IsPlanar G) (htriangle : IsTriangleFree G)
    (hsubcubic : IsSubcubic G) :
    ∃ color : V → Fin 20, IsPQColoring G 20 7 color := by sorry

end OPG401
