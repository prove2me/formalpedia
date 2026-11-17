-- Prove2me | Theorems.Thm_N25_Endgame_pointDiff_mem_M
-- name    : N25.Endgame.pointDiff_mem_M
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:13.890201+00:00
-- url     : https://prove2.me/theorems/29a0c5f4-5a4e-488a-8545-8e533e78f1e8
-- title:
--   Differences of rational geometric places are rational Jacobian classes
-- statement:
--   Let $P$ and $Q$ be geometric places of degree one that are fixed by every arithmetic Galois automorphism, and let $M$ be the arithmetic-Galois fixed subgroup of the level-$25$ Jacobian. Then their degree-zero divisor class satisfies
--
--   $$[P-Q]∈M.$$
--
--   This embeds rational geometric point differences into the group on which the reduction and finiteness arguments operate.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_PointDifference

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.pointDiff_mem_M
    (P Q : GPlace) (hP : IsRationalGeomPlace P)
    (hQ : IsRationalGeomPlace Q) :
    pointDiff P Q (hP.1.trans hQ.1.symm) ∈ N25.M := by sorry
