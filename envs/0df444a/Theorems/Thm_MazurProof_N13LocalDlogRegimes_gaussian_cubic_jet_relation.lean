-- Prove2me | Theorems.Thm_MazurProof_N13LocalDlogRegimes_gaussian_cubic_jet_relation
-- name    : MazurProof.N13LocalDlogRegimes.gaussian_cubic_jet_relation
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:51:46.825829+00:00
-- url     : https://prove2.me/theorems/dc3442a1-ab2e-4349-aecf-0c006271de73
-- title:
--   Mazur 13 port: gaussian_cubic_jet_relation
-- statement:
--   The Gaussian cubic relation remains valid in the first-jet quotient. This verifies directly that `i ↦ 1+ε` and `θ ↦ α` are compatible with the local presentation, rather than merely assigning two unrelated dual numbers.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13LocalDlogRegimes.lean#L60

import Mathlib
import Definitions.Def_MazurN13_L1

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13LocalDlogRegimes
open scoped CharTwo
open N13LocalDlogTwo
open TrivSqZeroExt

theorem MazurProof.N13LocalDlogRegimes.gaussian_cubic_jet_relation : thetaDual ^ 3 + 2 * thetaDual ^ 2 - thetaDual - 1 - gaussianIDual * (2 * thetaDual * (thetaDual + 1)) = 0 := by sorry
