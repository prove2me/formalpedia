-- Prove2me | Theorems.Thm_NumberField_Units_dirichletCoordinatesHom_injective
-- name    : NumberField.Units.dirichletCoordinatesHom_injective
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T05:52:58.002008+00:00
-- url     : https://prove2.me/theorems/a0c46aea-ad06-4029-aeaa-5a07c05b72b9
-- title:
--   Mazur 13 port: dirichletCoordinatesHom_injective
-- statement:
--   Supporting lemma `dirichletCoordinatesHom_injective` (namespace `NumberField.Units`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GaussianUnitSquareclasses.lean#L184

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NumberField NumberField.Units
open Finset Module
variable (K : Type*) [Field K] [NumberField K]

theorem NumberField.Units.dirichletCoordinatesHom_injective : Function.Injective (dirichletCoordinatesHom K) := by sorry
