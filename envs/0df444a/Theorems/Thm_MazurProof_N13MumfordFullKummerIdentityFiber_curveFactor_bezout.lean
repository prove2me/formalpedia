-- Prove2me | Theorems.Thm_MazurProof_N13MumfordFullKummerIdentityFiber_curveFactor_bezout
-- name    : MazurProof.N13MumfordFullKummerIdentityFiber.curveFactor_bezout
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:31:21.849054+00:00
-- url     : https://prove2.me/theorems/5f3db2af-445f-49eb-af35-42f4d1774b9c
-- title:
--   Mazur 13 port: curveFactor_bezout
-- statement:
--   If `f - L² = a w`, the complementary graph ideal is contained in `(a,Y-L)` whenever `a ∣ w`. Cantor's product formula then supplies the missing generator `Y-L` of the square. Thus no factorization of `a` is needed.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13MumfordFullKummerIdentityFiber.lean#L1474

import Mathlib
import Definitions.Def_MazurN13_L0

open MazurProof MazurProof.N13MumfordFullKummerIdentityFiber
open Polynomial
open SexticMumford
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K]

theorem MazurProof.N13MumfordFullKummerIdentityFiber.curveFactor_bezout (C : SexticMumford.Model K) (u₀ w L₀ : K[X]) (hu₀ : u₀ ≠ 0) (hcurve : C.f - L₀ ^ 2 = u₀ * w) : ∃ A B E : K[X], A * u₀ + B * (2 * L₀) + E * w = 1 := by sorry
