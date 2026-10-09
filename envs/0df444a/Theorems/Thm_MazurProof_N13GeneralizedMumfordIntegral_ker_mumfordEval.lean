-- Prove2me | Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_ker_mumfordEval
-- name    : MazurProof.N13GeneralizedMumfordIntegral.ker_mumfordEval
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:28:46.128993+00:00
-- url     : https://prove2.me/theorems/627e1449-4ccd-4dd1-9c88-467ba9b492f2
-- title:
--   Mazur 13 port: ker_mumfordEval
-- statement:
--   Supporting lemma `ker_mumfordEval` (namespace `MazurProof.N13GeneralizedMumfordIntegral`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GeneralizedMumfordIntegral.lean#L344

import Mathlib
import Definitions.Def_MazurN13_L0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GeneralizedMumfordIntegral
open Polynomial
universe u
variable {R : Type u} [CommRing R]

theorem MazurProof.N13GeneralizedMumfordIntegral.ker_mumfordEval [Nontrivial R] (D : SemiMumford (R := R)) : RingHom.ker (mumfordEval D) = mumfordIdeal D.u D.v := by sorry
