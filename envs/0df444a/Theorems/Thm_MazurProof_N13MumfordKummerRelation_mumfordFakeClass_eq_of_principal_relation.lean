-- Prove2me | Theorems.Thm_MazurProof_N13MumfordKummerRelation_mumfordFakeClass_eq_of_principal_relation
-- name    : MazurProof.N13MumfordKummerRelation.mumfordFakeClass_eq_of_principal_relation
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T05:10:14.495283+00:00
-- url     : https://prove2.me/theorems/98ffb895-bb38-457b-a534-e0e09cb392b8
-- title:
--   Mazur 13 port: mumfordFakeClass_eq_of_principal_relation
-- statement:
--   A principal relation between affine Mumford ideals preserves the raw fake-Kummer class. No degree split and no infinity-order hypothesis is needed.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13MumfordKummerRelation.lean#L682

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13MumfordKummerRelation
open Polynomial
open scoped nonZeroDivisors
open SexticMumford
attribute [local instance] MazurProof.N13MumfordKummerRelation.sexticAlgebraField

theorem MazurProof.N13MumfordKummerRelation.mumfordFakeClass_eq_of_principal_relation (D₁ D₂ : N13Mumford.Mumford ℚ) (α : Fˣ) (h : mumfordIdealUnit M D₁.toSemi * toPrincipalIdeal R F α = mumfordIdealUnit M D₂.toSemi) : N13MumfordKummerValue.mumfordFakeClass D₁ = N13MumfordKummerValue.mumfordFakeClass D₂ := by sorry
