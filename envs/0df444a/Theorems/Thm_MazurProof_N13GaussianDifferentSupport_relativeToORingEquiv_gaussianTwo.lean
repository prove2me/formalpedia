-- Prove2me | Theorems.Thm_MazurProof_N13GaussianDifferentSupport_relativeToORingEquiv_gaussianTwo
-- name    : MazurProof.N13GaussianDifferentSupport.relativeToORingEquiv_gaussianTwo
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T06:24:27.205987+00:00
-- url     : https://prove2.me/theorems/f6c56224-13d7-47d7-b6ee-2a2342a1955b
-- title:
--   Mazur 13 port: relativeToORingEquiv_gaussianTwo
-- statement:
--   Supporting lemma `relativeToORingEquiv_gaussianTwo` (namespace `MazurProof.N13GaussianDifferentSupport`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GaussianDifferentSupport.lean#L739

import Mathlib
import Definitions.Def_MazurN13_L3

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GaussianDifferentSupport
open Algebra Module Polynomial
open scoped nonZeroDivisors
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianDifferentSupport.fieldL
attribute [local instance] MazurProof.N13GaussianDifferentSupport.numberFieldL
attribute [local instance] MazurProof.N13GaussianDifferentSupport.dedekindO
attribute [local instance] MazurProof.N13GaussianDifferentSupport.fractionRingOL
attribute [local instance] MazurProof.N13GaussianDifferentSupport.intAlgebraO
attribute [local instance] MazurProof.N13GaussianDifferentSupport.dedekindRelativeO
attribute [local instance] MazurProof.N13GaussianDifferentSupport.torsionFreeGIL
attribute [local instance] MazurProof.N13GaussianDifferentSupport.torsionFreeRelativeO

theorem MazurProof.N13GaussianDifferentSupport.relativeToORingEquiv_gaussianTwo : relativeToORingEquiv (algebraMap GI RelativeO gaussianTwoInteger) = primeTwoInteger := by sorry
