-- Prove2me | Theorems.Thm_NumberField_Units_dirichletCoordinatesHom_surjective
-- name    : NumberField.Units.dirichletCoordinatesHom_surjective
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T05:56:00.371974+00:00
-- url     : https://prove2.me/theorems/fde660a3-b612-4be6-b07d-34dadc0bbf8d
-- title:
--   Mazur 13 port: dirichletCoordinatesHom_surjective
-- statement:
--   Supporting lemma `dirichletCoordinatesHom_surjective` (namespace `NumberField.Units`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GaussianUnitSquareclasses.lean#L176

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NumberField NumberField.Units
open Finset Module
variable (K : Type*) [Field K] [NumberField K]

theorem NumberField.Units.dirichletCoordinatesHom_surjective : Function.Surjective (dirichletCoordinatesHom K) := by sorry
