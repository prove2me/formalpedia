-- Prove2me | Theorems.Thm_MazurProof_N13MumfordFullKummerIdentityFiber_exists_pade_graph_scalar_of_c_ne_zero_degree_one
-- name    : MazurProof.N13MumfordFullKummerIdentityFiber.exists_pade_graph_scalar_of_c_ne_zero_degree_one
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:46:32.965854+00:00
-- url     : https://prove2.me/theorems/2e1447aa-ae7c-471e-92f6-d2ccd8518d25
-- title:
--   Mazur 13 port: exists_pade_graph_scalar_of_c_ne_zero_degree_one
-- statement:
--   When `u` has degree one, the same graph scalar follows from the fact that a monic linear quotient is the ground field itself. No norm calculation is needed in this degeneration.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13MumfordFullKummerIdentityFiber.lean#L1276

import Mathlib
import Definitions.Def_MazurN13_L1

open MazurProof MazurProof.N13MumfordFullKummerIdentityFiber
open Polynomial
open SexticMumford
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K]

theorem MazurProof.N13MumfordFullKummerIdentityFiber.exists_pade_graph_scalar_of_c_ne_zero_degree_one (D : LowRep) (q : ℚˣ) (a l : ℚ[X]) (c : ℚ) (hrelation : Polynomial.C (q : ℚ) * l ^ 2 - a ^ 2 * D.toSemi.u = Polynomial.C c * N13Mumford.f ℚ) (hu1 : D.toSemi.u.natDegree = 1) (hc : c ≠ 0) : ∃ b : ℚ, b ≠ 0 ∧ b ^ 2 = c / (q : ℚ) ∧ D.toSemi.u ∣ l - Polynomial.C b * D.toSemi.v := by sorry
