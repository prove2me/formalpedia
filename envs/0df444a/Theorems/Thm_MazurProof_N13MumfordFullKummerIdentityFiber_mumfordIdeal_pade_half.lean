-- Prove2me | Theorems.Thm_MazurProof_N13MumfordFullKummerIdentityFiber_mumfordIdeal_pade_half
-- name    : MazurProof.N13MumfordFullKummerIdentityFiber.mumfordIdeal_pade_half
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:30:55.997012+00:00
-- url     : https://prove2.me/theorems/5d699618-9509-4957-9fa5-ac4bc33614e4
-- title:
--   Mazur 13 port: mumfordIdeal_pade_half
-- statement:
--   The exact finite-ideal identity produced by a Padé half. The two Bézout hypotheses are the smooth Cantor transversality conditions for the intermediate graph ideals. The conclusion already identifies the target Mumford ideal with a square up to the principal graph function `Y-L`.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13MumfordFullKummerIdentityFiber.lean#L1619

import Mathlib
import Definitions.Def_MazurN13_L0

open MazurProof MazurProof.N13MumfordFullKummerIdentityFiber
open Polynomial
open SexticMumford
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K]

theorem MazurProof.N13MumfordFullKummerIdentityFiber.mumfordIdeal_pade_half (C : SexticMumford.Model K) (a u₀ v₀ L₀ : K[X]) (κ : Kˣ) (hcurve : C.f - L₀ ^ 2 = a ^ 2 * (Polynomial.C (κ : K) * u₀)) (hgraph : u₀ ∣ L₀ - v₀) (ha : a ≠ 0) : mumfordIdeal C a L₀ ^ 2 * mumfordIdeal C u₀ v₀ = Ideal.span ({ySubClass C L₀} : Set (SexticMumford.CoordinateRing C)) := by sorry
