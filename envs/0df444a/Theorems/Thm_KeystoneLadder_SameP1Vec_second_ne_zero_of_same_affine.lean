-- Prove2me | Theorems.Thm_KeystoneLadder_SameP1Vec_second_ne_zero_of_same_affine
-- name    : KeystoneLadder.SameP1Vec.second_ne_zero_of_same_affine
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:05:26.87319+00:00
-- url     : https://prove2.me/theorems/433d17cc-3d78-4cff-9eee-876ec7c43066
-- title:
--   An affine projective representative has nonzero second coordinate
-- statement:
--   Let $k$ be a field, let $x∈k$, and let $v=(v_0,v_1)∈k^2$. If the affine representative $(x,1)$ is projectively equivalent to $v$, in the oriented sense that $v=c(x,1)$ for some $c≠0$, then $$v_1≠0.$$ This distinguishes affine x-coordinates from the infinity branch in the total ladder. Formalization note: decidable equality on $k$ is used for executable case distinctions.
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

theorem KeystoneLadder.SameP1Vec.second_ne_zero_of_same_affine {x : k} {v : Fin 2 → k}
    (h : SameP1Vec (![x, 1] : Fin 2 → k) v) : v 1 ≠ 0 := by sorry
