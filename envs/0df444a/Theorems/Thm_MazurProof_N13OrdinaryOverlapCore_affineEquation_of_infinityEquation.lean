-- Prove2me | Theorems.Thm_MazurProof_N13OrdinaryOverlapCore_affineEquation_of_infinityEquation
-- name    : MazurProof.N13OrdinaryOverlapCore.affineEquation_of_infinityEquation
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:25:15.494778+00:00
-- url     : https://prove2.me/theorems/c5c6f8af-af11-4e8f-8825-4feb55782d92
-- title:
--   Mazur 13 port: affineEquation_of_infinityEquation
-- statement:
--   The infinity equation implies the affine equation after substituting `x = t⁻¹` and `y = t⁻³v`.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13OrdinaryOverlapCore.lean#L22

import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem MazurProof.N13OrdinaryOverlapCore.affineEquation_of_infinityEquation {S : Type*} [CommRing S] (t x v : S) (htx : t * x = 1) (hInfinity : v ^ 2 + (1 + t ^ 2 + t ^ 3) * v = t + t ^ 2) : (x ^ 3 * v) ^ 2 + (x ^ 3 + x + 1) * (x ^ 3 * v) = x ^ 5 + x ^ 4 := by sorry
