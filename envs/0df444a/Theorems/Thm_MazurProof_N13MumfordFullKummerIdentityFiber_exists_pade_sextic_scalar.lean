-- Prove2me | Theorems.Thm_MazurProof_N13MumfordFullKummerIdentityFiber_exists_pade_sextic_scalar
-- name    : MazurProof.N13MumfordFullKummerIdentityFiber.exists_pade_sextic_scalar
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T08:12:25.049047+00:00
-- url     : https://prove2.me/theorems/a8f365c0-5c3a-401a-8d67-918676b4b183
-- title:
--   Mazur 13 port: exists_pade_sextic_scalar
-- statement:
--   The Padé kernel turns the branch-algebra congruence into a single sextic polynomial identity. Degree at most six makes the quotient by the monic sextic a scalar.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13MumfordFullKummerIdentityFiber.lean#L359

import Mathlib
import Definitions.Def_MazurN13_L4

open MazurProof MazurProof.N13MumfordFullKummerIdentityFiber
open Polynomial
open SexticMumford
open scoped nonZeroDivisors

theorem MazurProof.N13MumfordFullKummerIdentityFiber.exists_pade_sextic_scalar (D : LowRep) (β : Lˣ) (q : ℚˣ) (hfst : N13MumfordKummerValue.uThetaUnit (N13LowDegreeKummerHom.asMumford D) = β ^ 2 * N13FullNormPair.scalarUnits q) (a : Polynomial.degreeLT ℚ 3) (ha0 : a ≠ 0) (haKer : padeHighCoeffMap (branchSquarePolynomial β) a = 0) : ∃ c : ℚ, Polynomial.C (q : ℚ) * (padeRemainderMap (branchSquarePolynomial β) a) ^ 2 - (a : ℚ[X]) ^ 2 * D.toSemi.u = Polynomial.C c * N13Mumford.f ℚ := by sorry
