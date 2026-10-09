-- Prove2me | Theorems.Thm_MazurProof_N13MumfordFullKummerIdentityFiber_mumfordIdeal_sq_eq_square_generator
-- name    : MazurProof.N13MumfordFullKummerIdentityFiber.mumfordIdeal_sq_eq_square_generator
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:31:14.915749+00:00
-- url     : https://prove2.me/theorems/1dd21459-606c-4a48-9fd8-6a34b113835e
-- title:
--   Mazur 13 port: mumfordIdeal_sq_eq_square_generator
-- statement:
--   Supporting lemma `mumfordIdeal_sq_eq_square_generator` (namespace `MazurProof.N13MumfordFullKummerIdentityFiber`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13MumfordFullKummerIdentityFiber.lean#L1532

import Mathlib
import Definitions.Def_MazurN13_L0

open MazurProof MazurProof.N13MumfordFullKummerIdentityFiber
open Polynomial
open SexticMumford
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K]

theorem MazurProof.N13MumfordFullKummerIdentityFiber.mumfordIdeal_sq_eq_square_generator (C : SexticMumford.Model K) (a w L₀ : K[X]) (hcurve : C.f - L₀ ^ 2 = a * w) (haw : a ∣ w) (hbezout : ∃ A B E : K[X], A * a + B * (2 * L₀) + E * w = 1) : mumfordIdeal C a L₀ ^ 2 = mumfordIdeal C (a ^ 2) L₀ := by sorry
