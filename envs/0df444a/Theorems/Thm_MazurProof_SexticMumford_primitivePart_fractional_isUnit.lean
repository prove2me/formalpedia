-- Prove2me | Theorems.Thm_MazurProof_SexticMumford_primitivePart_fractional_isUnit
-- name    : MazurProof.SexticMumford.primitivePart_fractional_isUnit
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T05:50:42.271004+00:00
-- url     : https://prove2.me/theorems/8155cfdc-03ab-4c6d-8aa3-2bc50b4ac4de
-- title:
--   Mazur 13 port: primitivePart_fractional_isUnit
-- statement:
--   Supporting lemma `primitivePart_fractional_isUnit` (namespace `MazurProof.SexticMumford`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/SexticMumfordPrimitivePart.lean#L233

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.SexticMumford
open Polynomial
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K]
variable (M : Model K)

theorem MazurProof.SexticMumford.primitivePart_fractional_isUnit (J : Ideal (CoordinateRing M)) (hJ : IsUnit (J : FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))) : IsUnit (primitivePart M J (contentGenerator M J) : FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by sorry
