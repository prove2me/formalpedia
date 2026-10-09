-- Prove2me | Theorems.Thm_MazurProof_N13InfinityBaseChange_infinityCompatible
-- name    : MazurProof.N13InfinityBaseChange.infinityCompatible
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T08:07:34.67383+00:00
-- url     : https://prove2.me/theorems/93a2a621-7e94-4d10-9c79-6a65491ee4f0
-- title:
--   Mazur 13 port: infinityCompatible
-- statement:
--   Every injective characteristic-zero coefficient extension preserves the chosen positive infinity order on the N13 sextic.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13InfinityBaseChange.lean#L242

import Mathlib
import Definitions.Def_MazurN13_L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13InfinityBaseChange
open Polynomial
open scoped LaurentSeries
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K'] [CharZero K] [CharZero K']

theorem MazurProof.N13InfinityBaseChange.infinityCompatible (ι : K →+* K') (hι : Function.Injective ι) : SexticMumford.OrientedBaseChange.InfinityCompatible ι hι (map_n13_f ι) (N13Infinity.positiveInfinityOrder K) (N13Infinity.positiveInfinityOrder K') := by sorry
