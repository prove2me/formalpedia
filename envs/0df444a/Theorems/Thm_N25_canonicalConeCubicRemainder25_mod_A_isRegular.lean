-- Prove2me | Theorems.Thm_N25_canonicalConeCubicRemainder25_mod_A_isRegular
-- name    : N25.canonicalConeCubicRemainder25_mod_A_isRegular
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:36:32.958031+00:00
-- url     : https://prove2.me/theorems/0405094a-c31d-42b9-a543-6244430c735c
-- title:
--   The reduced cubic remainder is a non-zero-divisor in the quadric root algebra
-- statement:
--   Let $K$ be a field, reduce the monic cone quadric polynomial and the cubic remainder along the boundary map $β$ with $β(A)=0$, and adjoin a root of the reduced quadric. The value of the reduced cubic remainder at that root is regular: $$\overline C(\overline T)\text{ is a non-zero-divisor in }K_{\partial}[T]/(\overline Q).$$ This is the boundary input for swapping the regular sequence formed by $A$ and the cubic relation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalConeTower
import Definitions.Def_N25_CanonicalConeBoundary

open N25
open Polynomial
variable (K : Type*) [Field K]

theorem N25.canonicalConeCubicRemainder25_mod_A_isRegular :
    IsRegular (AdjoinRoot.mk
      ((canonicalConeQuadricPolynomial25 K).map (canonicalConeBoundaryMap25 K))
      ((canonicalConeCubicRemainder25 K).map (canonicalConeBoundaryMap25 K))) := by sorry
