-- Prove2me | Theorems.Thm_KeystoneLadder_XOnly_xLadderRep_correct_seam
-- name    : KeystoneLadder.XOnly.xLadderRep_correct_seam
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:06:54.291317+00:00
-- url     : https://prove2.me/theorems/4b329434-b024-4d9b-8364-16953613da26
-- title:
--   The x-only ladder represents the x-coordinate of every multiple
-- statement:
--   Let $k$ be a field, let $E$ be a Weierstrass curve over $k$, and let $P=(x,y)$ be a nonsingular affine point. For $n∈ℕ$, let $xRep(nP)∈k^2$ be the homogeneous x-coordinate of the multiple $nP$, with the identity represented by $(1,0)$, and let $L_E(x,n)$ be the total x-only ladder output. Then $$xRep(nP)∼L_E(x,n).$$ This is the seam theorem asserting correctness even through degenerate differential-addition steps. Formalization note: decidable equality on $k$ is needed by the total recursive algorithm.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_KeystoneLadder

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.overlappingInstances false
open Polynomial
open WeierstrassCurve
open WeierstrassCurve.Affine
open KeystoneLadder
universe u
variable {k : Type u} [Field k] [DecidableEq k]
variable (E : WeierstrassCurve k)
open KeystoneLadder.XOnly

theorem KeystoneLadder.XOnly.xLadderRep_correct_seam {x y : k}
    (h : E.toAffine.Nonsingular x y) (n : ℕ) :
    SameP1Vec
      ((n • (Point.some x y h : E.toAffine.Point)).xRep)
      (xLadderRep E x n) := by sorry
