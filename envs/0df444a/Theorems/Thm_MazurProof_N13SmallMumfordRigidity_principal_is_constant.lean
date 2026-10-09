-- Prove2me | Theorems.Thm_MazurProof_N13SmallMumfordRigidity_principal_is_constant
-- name    : MazurProof.N13SmallMumfordRigidity.principal_is_constant
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T05:21:47.725216+00:00
-- url     : https://prove2.me/theorems/dbfebe5e-0119-4ad0-bafb-e6ac33d2f2c0
-- title:
--   Mazur 13 port: principal_is_constant
-- statement:
--   Supporting lemma `principal_is_constant` (namespace `MazurProof.N13SmallMumfordRigidity`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13SmallMumfordRigidity.lean#L129

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof
open Polynomial
open scoped LaurentSeries nonZeroDivisors
universe u
variable (K : Type u) [Field K] [CharZero K]
open SexticMumford

theorem MazurProof.N13SmallMumfordRigidity.principal_is_constant (D₁ D₂ : Mumford (N13Mumford.model K)) (α : (N13Mumford.FunctionField K)ˣ) (hIdeal : mumfordIdealUnit (N13Mumford.model K) D₁.toSemi * toPrincipalIdeal (N13Mumford.CoordinateRing K) (N13Mumford.FunctionField K) α = mumfordIdealUnit (N13Mumford.model K) D₂.toSemi) (hInf : Multiplicative.ofAdd ((D₁.nInf : ℤ) - 1) * (N13Infinity.positiveInfinityOrder K).ordPlus α = Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1)) : ∃ c : Kˣ, α = N13Infinity.functionConstUnit K c := by sorry
