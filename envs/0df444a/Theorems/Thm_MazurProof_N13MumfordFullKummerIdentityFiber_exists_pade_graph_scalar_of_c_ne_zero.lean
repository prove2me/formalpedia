-- Prove2me | Theorems.Thm_MazurProof_N13MumfordFullKummerIdentityFiber_exists_pade_graph_scalar_of_c_ne_zero
-- name    : MazurProof.N13MumfordFullKummerIdentityFiber.exists_pade_graph_scalar_of_c_ne_zero
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T08:07:40.275995+00:00
-- url     : https://prove2.me/theorems/fd99765d-bc66-42de-abc1-f5d0120bd5e3
-- title:
--   Mazur 13 port: exists_pade_graph_scalar_of_c_ne_zero
-- statement:
--   If the scalar `c` is nonzero and `u` has its generic quadratic degree, the Padé quotient `l/v` is rigid. Its square and its algebra norm both equal `c/q`, so Cayley--Hamilton forces it to be a rational scalar `b`. Equivalently, `l ≡ b v (mod u)`.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13MumfordFullKummerIdentityFiber.lean#L1134

import Mathlib
import Definitions.Def_MazurN13_L4

open MazurProof MazurProof.N13MumfordFullKummerIdentityFiber
open Polynomial
open SexticMumford
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K]

theorem MazurProof.N13MumfordFullKummerIdentityFiber.exists_pade_graph_scalar_of_c_ne_zero (D : LowRep) (β : Lˣ) (q : ℚˣ) (a : Polynomial.degreeLT ℚ 3) (ha0 : a ≠ 0) (haKer : padeHighCoeffMap (branchSquarePolynomial β) a = 0) (c : ℚ) (hrelation : Polynomial.C (q : ℚ) * (padeRemainderMap (branchSquarePolynomial β) a) ^ 2 - (a : ℚ[X]) ^ 2 * D.toSemi.u = Polynomial.C c * N13Mumford.f ℚ) (hsnd : (-1 : ℚˣ) * N13MumfordKummerNorm.normRootUnit D = N13FullNormPair.normUnits β * q ^ 3) (hu2 : D.toSemi.u.natDegree = 2) (hc : c ≠ 0) : ∃ b : ℚ, b ≠ 0 ∧ b ^ 2 = c / (q : ℚ) ∧ D.toSemi.u ∣ padeRemainderMap (branchSquarePolynomial β) a - Polynomial.C b * D.toSemi.v := by sorry
