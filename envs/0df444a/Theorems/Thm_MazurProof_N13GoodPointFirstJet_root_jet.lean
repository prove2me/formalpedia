-- Prove2me | Theorems.Thm_MazurProof_N13GoodPointFirstJet_root_jet
-- name    : MazurProof.N13GoodPointFirstJet.root_jet
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:32:13.570357+00:00
-- url     : https://prove2.me/theorems/68a55c80-4984-4724-874b-f5e51319bf69
-- title:
--   Mazur 13 port: root_jet
-- statement:
--   Supporting lemma `root_jet` (namespace `MazurProof.N13GoodPointFirstJet`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GoodPointFirstJet.lean#L44

import Mathlib
import Definitions.Def_MazurN13_L0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GoodPointFirstJet
open Polynomial MulOpposite
universe u
variable {K : Type u} [Field K]

theorem MazurProof.N13GoodPointFirstJet.root_jet (x y s : K) (hc : y ^ 2 + (x ^ 3 + x + 1) * y - (x ^ 5 + x ^ 4) = 0) (hd : (2 * y + (x ^ 3 + x + 1)) * s + (3 * x ^ 2 + 1) * y - (5 * x ^ 4 + 4 * x ^ 3) = 0) : (N13GeneralizedMumfordIntegral.curvePoly (R := K)).eval₂ (polynomialJet x) (y, s) = 0 := by sorry
