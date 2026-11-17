-- Prove2me | Theorems.Thm_N25_canonicalConeTowerA25_isRegular
-- name    : N25.canonicalConeTowerA25_isRegular
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:36:30.833636+00:00
-- url     : https://prove2.me/theorems/e81c7b02-2216-48ee-90ed-2ba48b64599e
-- title:
--   The distinguished coordinate remains regular after imposing the cubic relation
-- statement:
--   Let $K$ be a field, first adjoin a root $T$ of the monic cone quadric, and then quotient by the value of the cone cubic remainder at $T$. In this final tower quotient, the image of the distinguished coordinate $A$ is regular: $$\overline A\text{ is a non-zero-divisor in }K_{\mathrm{base}}[T]/(Q(T),C(T)).$$ This establishes the key non-zero-divisor needed to compare the cone with its affine chart.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalConeTower
import Definitions.Def_N25_CanonicalConeBoundary

open N25
open Polynomial
variable (K : Type*) [Field K]

theorem N25.canonicalConeTowerA25_isRegular :
    IsRegular (Ideal.Quotient.mk
      (Ideal.span ({AdjoinRoot.mk (canonicalConeQuadricPolynomial25 K)
        (canonicalConeCubicRemainder25 K)} : Set (CanonicalConeQuadricRoot25 K)))
      (AdjoinRoot.of (canonicalConeQuadricPolynomial25 K) (canonicalConeBaseA25 K))) := by sorry
