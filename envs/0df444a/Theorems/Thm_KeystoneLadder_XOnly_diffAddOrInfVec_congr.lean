-- Prove2me | Theorems.Thm_KeystoneLadder_XOnly_diffAddOrInfVec_congr
-- name    : KeystoneLadder.XOnly.diffAddOrInfVec_congr
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:06:48.289304+00:00
-- url     : https://prove2.me/theorems/1bca84d5-96aa-4588-921b-c82725daad02
-- title:
--   Total differential addition respects projective representatives
-- statement:
--   Let $k$ be a field and let $E$ be a Weierstrass curve over $k$. For vectors $A,B,D∈k^2$, let $A_E(A,B,D)$ denote the total homogeneous differential-addition operation, including its point-at-infinity branch. If $A∼A'$, $B∼B'$, and $D∼D'$, then $$A_E(A,B,D)∼A_E(A',B',D').$$ Thus differential addition descends from raw vector representatives to projective x-coordinates. Formalization note: decidable equality on $k$ is needed to execute the degenerate branch.
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

theorem KeystoneLadder.XOnly.diffAddOrInfVec_congr
    {A A' B B' D D' : Fin 2 → k}
    (hA : SameP1Vec A A') (hB : SameP1Vec B B') (hD : SameP1Vec D D') :
    SameP1Vec (diffAddOrInfVec E A B D) (diffAddOrInfVec E A' B' D') := by sorry
