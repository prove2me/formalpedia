-- Prove2me | Theorems.Thm_KeystoneLadder_XOnly_xLadderRep_four
-- name    : KeystoneLadder.XOnly.xLadderRep_four
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:06:44.239444+00:00
-- url     : https://prove2.me/theorems/b16703af-f104-41d1-88fe-03bdf8599865
-- title:
--   The fourth x-only ladder step is double doubling
-- statement:
--   Let $k$ be a field, let $E$ be a Weierstrass curve over $k$, let $x∈k$, put $a_x=(x,1)$, and let $D_E$ and $L_E$ denote homogeneous doubling and the x-only ladder representative. Then $$L_E(x,4)=D_E(D_E(a_x)).$$ This explicit base case anchors the even branch of the ladder and its comparison with division polynomials. Formalization note: decidable equality on $k$ is part of the executable ladder carrier.
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
theorem KeystoneLadder.XOnly.xLadderRep_four (x : k) :
    xLadderRep E x 4 = doubleVec E (doubleVec E (xAffVec x)) := by sorry
