-- Prove2me | Theorems.Thm_MazurProof_N13OrdinaryOverlapCore_infinityEquation_of_affineEquation
-- name    : MazurProof.N13OrdinaryOverlapCore.infinityEquation_of_affineEquation
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:24:54.692112+00:00
-- url     : https://prove2.me/theorems/e8c1b6c5-ad41-4039-bbfc-255eccd6bc42
-- title:
--   Mazur 13 port: infinityEquation_of_affineEquation
-- statement:
--   The affine equation implies the infinity equation after substituting `t = x⁻¹` and `v = t³y`.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13OrdinaryOverlapCore.lean#L62

import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem MazurProof.N13OrdinaryOverlapCore.infinityEquation_of_affineEquation {S : Type*} [CommRing S] (x t y : S) (hxt : x * t = 1) (hAffine : y ^ 2 + (x ^ 3 + x + 1) * y = x ^ 5 + x ^ 4) : (t ^ 3 * y) ^ 2 + (1 + t ^ 2 + t ^ 3) * (t ^ 3 * y) = t + t ^ 2 := by sorry
