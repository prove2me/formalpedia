-- Prove2me | Theorems.Thm_MazurProof_N13SpecialCertifiedNumerator_dvd_fixed_support
-- name    : MazurProof.N13SpecialCertifiedNumerator.dvd_fixed_support
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:32:05.142643+00:00
-- url     : https://prove2.me/theorems/079f629f-758b-422e-ac5b-032638ce1965
-- title:
--   Mazur 13 port: dvd_fixed_support
-- statement:
--   Supporting lemma `dvd_fixed_support` (namespace `MazurProof.N13SpecialCertifiedNumerator`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13SpecialCertifiedNumerator.lean#L35

import Mathlib
import Definitions.Def_MazurN13_L0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialDivisorCharts
open N13SpecialComparisonFactorPair

theorem MazurProof.N13SpecialCertifiedNumerator.dvd_fixed_support (p : K[X]) (i j : ℕ) (hij : i + j ≤ 16) (hp : p ∣ X ^ i * (X - 1) ^ j) : p ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by sorry
