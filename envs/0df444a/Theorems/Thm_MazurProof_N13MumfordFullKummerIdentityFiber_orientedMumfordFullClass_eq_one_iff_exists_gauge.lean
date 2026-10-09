-- Prove2me | Theorems.Thm_MazurProof_N13MumfordFullKummerIdentityFiber_orientedMumfordFullClass_eq_one_iff_exists_gauge
-- name    : MazurProof.N13MumfordFullKummerIdentityFiber.orientedMumfordFullClass_eq_one_iff_exists_gauge
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T08:12:30.28687+00:00
-- url     : https://prove2.me/theorems/89ae9817-8781-4a04-a354-57dfe26b7666
-- title:
--   Mazur 13 port: orientedMumfordFullClass_eq_one_iff_exists_gauge
-- statement:
--   Equality to one in the full target is exactly membership in the product of the square/norm and scalar/cubic gauges.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13MumfordFullKummerIdentityFiber.lean#L57

import Mathlib
import Definitions.Def_MazurN13_L4

open MazurProof MazurProof.N13MumfordFullKummerIdentityFiber
open Polynomial
open SexticMumford
open scoped nonZeroDivisors

theorem MazurProof.N13MumfordFullKummerIdentityFiber.orientedMumfordFullClass_eq_one_iff_exists_gauge (D : LowRep) : N13MumfordOrientedFullKummer.orientedMumfordFullClass D = 1 ↔ ∃ β : Lˣ, ∃ q : ℚˣ, N13MumfordOrientedFullKummer.orientedMumfordNormPair D = EvenSexticNormPair.chi N13FullNormPair.normUnits β * EvenSexticNormPair.iota N13FullNormPair.normUnits N13FullNormPair.scalarUnits N13FullNormPair.normUnits_scalarUnits q := by sorry
