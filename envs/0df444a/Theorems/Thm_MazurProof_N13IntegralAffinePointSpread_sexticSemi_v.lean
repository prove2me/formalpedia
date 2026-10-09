-- Prove2me | Theorems.Thm_MazurProof_N13IntegralAffinePointSpread_sexticSemi_v
-- name    : MazurProof.N13IntegralAffinePointSpread.sexticSemi_v
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T04:50:05.128605+00:00
-- url     : https://prove2.me/theorems/a80ef709-6bd2-4025-a662-de68046b7ed1
-- title:
--   Mazur 13 port: sexticSemi_v
-- statement:
--   Supporting lemma `sexticSemi_v` (namespace `MazurProof.N13IntegralAffinePointSpread`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13IntegralAffinePointSpread.lean#L137

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13IntegralAffinePointSpread
open Polynomial
attribute [local instance] MazurProof.N13IntegralAffinePointSpread.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13IntegralAffinePointSpread.sexticSemi_v (P : IntegralPoint) : (N13TwoAdicMumfordTransport.sexticSemiOfSemi (integralSemiGraph P) 0).v = C (sexticY P) := by sorry
