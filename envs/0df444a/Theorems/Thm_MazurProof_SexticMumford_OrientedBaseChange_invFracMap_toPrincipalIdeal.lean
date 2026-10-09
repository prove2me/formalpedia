-- Prove2me | Theorems.Thm_MazurProof_SexticMumford_OrientedBaseChange_invFracMap_toPrincipalIdeal
-- name    : MazurProof.SexticMumford.OrientedBaseChange.invFracMap_toPrincipalIdeal
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T08:22:32.150986+00:00
-- url     : https://prove2.me/theorems/2bf38146-5b34-4598-bb2c-0a46378446c9
-- title:
--   Mazur 13 port: invFracMap_toPrincipalIdeal
-- statement:
--   Supporting lemma `invFracMap_toPrincipalIdeal` (namespace `MazurProof.SexticMumford.OrientedBaseChange`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/SexticMumfordOrientedBaseChange.lean#L206

import Mathlib
import Definitions.Def_MazurN13_L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.SexticMumford MazurProof.SexticMumford.OrientedBaseChange
open Polynomial
open scoped nonZeroDivisors
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}

theorem MazurProof.SexticMumford.OrientedBaseChange.invFracMap_toPrincipalIdeal (ι : K →+* K') (hι : Function.Injective ι) (hM : M.f.map ι = M'.f) (α : (FunctionField M)ˣ) : invFracMap ι hι hM (toPrincipalIdeal (CoordinateRing M) (FunctionField M) α) = toPrincipalIdeal (CoordinateRing M') (FunctionField M') (functionUnitMap ι hι hM α) := by sorry
