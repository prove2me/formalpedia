-- Prove2me | Theorems.Thm_KeystoneLadder_SameP1Vec_second_eq_zero_of_same_infty
-- name    : KeystoneLadder.SameP1Vec.second_eq_zero_of_same_infty
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:05:23.450461+00:00
-- url     : https://prove2.me/theorems/70e3b3db-e6eb-48ec-bf48-d367bbf0a7d6
-- title:
--   A representative of infinity has zero second coordinate
-- statement:
--   Let $k$ be a field, let $v=(v_0,v_1)∈k^2$, and let $[1:0]$ be the homogeneous representative of the point at infinity on the x-line. If $[1:0]∼v$, meaning $v$ is a nonzero scalar multiple of $(1,0)$, then $$v_1=0.$$ This identifies the infinity branch of the projective ladder from its denominator coordinate. Formalization note: decidable equality on $k$ supports the executable branch tests.
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
open KeystoneLadder.SameP1Vec

theorem KeystoneLadder.SameP1Vec.second_eq_zero_of_same_infty {v : Fin 2 → k}
    (h : SameP1Vec (![1, 0] : Fin 2 → k) v) : v 1 = 0 := by sorry
