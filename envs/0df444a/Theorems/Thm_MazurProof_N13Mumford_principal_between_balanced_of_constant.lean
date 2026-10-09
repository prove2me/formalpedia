-- Prove2me | Theorems.Thm_MazurProof_N13Mumford_principal_between_balanced_of_constant
-- name    : MazurProof.N13Mumford.principal_between_balanced_of_constant
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T05:01:29.65164+00:00
-- url     : https://prove2.me/theorems/f7bc75bb-9a63-45c2-85e6-6db715415dc1
-- title:
--   Mazur 13 port: principal_between_balanced_of_constant
-- statement:
--   Supporting lemma `principal_between_balanced_of_constant` (namespace `MazurProof.N13Mumford`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13MumfordRigidity.lean#L34

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13Mumford
open scoped nonZeroDivisors
open SexticMumford
universe u
variable (K : Type u) [Field K] [CharZero K]

theorem MazurProof.N13Mumford.principal_between_balanced_of_constant {D₁ D₂ : Mumford K} {α : (FunctionField K)ˣ} (c : Kˣ) (hα : α = N13Infinity.functionConstUnit K c) (hIdeal : mumfordIdealUnit (model K) D₁.toSemi * toPrincipalIdeal (CoordinateRing K) (FunctionField K) α = mumfordIdealUnit (model K) D₂.toSemi) (hInf : Multiplicative.ofAdd ((D₁.nInf : ℤ) - 1) * (N13Infinity.positiveInfinityOrder K).ordPlus α = Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1)) : D₁ = D₂ := by sorry
