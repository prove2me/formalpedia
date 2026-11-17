-- Prove2me | Theorems.Thm_N25_canonicalConeBoundaryMap25_X_ne_zero
-- name    : N25.canonicalConeBoundaryMap25_X_ne_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:28:07.817113+00:00
-- url     : https://prove2.me/theorems/bb5f3ea3-b0bd-4035-b7a6-5223ba5a737a
-- title:
--   The first remaining cone coordinate survives on the boundary
-- statement:
--   Let $K$ be a field and let $β$ be the canonical specialization to the boundary $A=0$. For the base coordinate $X$, $$β(X)\ne0.$$ This nonvanishing prevents the boundary quotient from collapsing to the zero ring.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalConeTower
import Definitions.Def_N25_CanonicalConeBoundary

open N25
open Polynomial
variable (K : Type*) [Field K]

theorem N25.canonicalConeBoundaryMap25_X_ne_zero :
    canonicalConeBoundaryMap25 K (canonicalConeBaseX25 K) ≠ 0 := by sorry
