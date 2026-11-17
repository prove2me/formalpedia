-- Prove2me | Theorems.Thm_N25_canonicalConeQuadricPolynomial25_monic
-- name    : N25.canonicalConeQuadricPolynomial25_monic
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:28:01.454629+00:00
-- url     : https://prove2.me/theorems/300eecd9-4c48-4b05-8935-2a743d908a07
-- title:
--   The cone quadric is monic in the tower variable
-- statement:
--   Let $K$ be a field and write the canonical cone quadric as a one-variable polynomial over the chosen base coordinate ring. Then $$Q_{\mathrm{tower}}(T)\text{ is monic}.$$ This permits the cone to be represented by adjoining a root without introducing scalar torsion.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalConeTower
import Definitions.Def_N25_CanonicalConeBoundary

open N25
open Polynomial
variable (K : Type*) [Field K]

theorem N25.canonicalConeQuadricPolynomial25_monic : (canonicalConeQuadricPolynomial25 K).Monic := by sorry
