-- Prove2me | Theorems.Thm_KeystoneLadder_XOnly_xLadderRep_three
-- name    : KeystoneLadder.XOnly.xLadderRep_three
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:06:48.469274+00:00
-- url     : https://prove2.me/theorems/8db53a44-252e-4594-9420-640d85774a89
-- title:
--   The third x-only ladder step is differential addition after doubling
-- statement:
--   Let $k$ be a field, let $E$ be a Weierstrass curve over $k$, let $x∈k$, put $a_x=(x,1)$, let $D_E$ be homogeneous doubling, let $A_E$ be total differential addition, and let $L_E(x,n)$ be the raw x-only ladder representative at index $n$. Then $$L_E(x,3)=A_E(a_x,D_E(a_x),a_x).$$ This explicit base case anchors the odd branch of the ladder correctness argument. Formalization note: decidable equality on $k$ is used by the total addition branch.
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

@[simp]
theorem KeystoneLadder.XOnly.xLadderRep_three (x : k) :
    xLadderRep E x 3 =
      diffAddOrInfVec E (xAffVec x) (doubleVec E (xAffVec x)) (xAffVec x) := by sorry
