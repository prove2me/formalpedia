-- Prove2me | Theorems.Thm_MazurProof_N13GaussianNamedUnitSquareclasses_relativeZeta_sq
-- name    : MazurProof.N13GaussianNamedUnitSquareclasses.relativeZeta_sq
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T06:32:29.756978+00:00
-- url     : https://prove2.me/theorems/30127d01-9f25-4c1b-823b-081c7cdbed53
-- title:
--   Mazur 13 port: relativeZeta_sq
-- statement:
--   Supporting lemma `relativeZeta_sq` (namespace `MazurProof.N13GaussianNamedUnitSquareclasses`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GaussianNamedUnitSquareclasses.lean#L88

import Mathlib
import Definitions.Def_MazurN13_L3

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GaussianNamedUnitSquareclasses
open Function
open Polynomial
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.hKIrreducibleFact
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.intAlgebraL
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.intAlgebraGI
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.intAlgebraRelativeO
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.intAlgebraAbsoluteO

theorem MazurProof.N13GaussianNamedUnitSquareclasses.relativeZeta_sq : relativeZeta ^ 2 = (-1 : RelativeO) := by sorry
