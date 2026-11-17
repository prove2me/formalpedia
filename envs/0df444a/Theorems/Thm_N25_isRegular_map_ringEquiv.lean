-- Prove2me | Theorems.Thm_N25_isRegular_map_ringEquiv
-- name    : N25.isRegular_map_ringEquiv
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:26.292203+00:00
-- url     : https://prove2.me/theorems/8534d9a5-6a28-471a-8136-acfb6d873ed4
-- title:
--   Ring equivalences preserve regular elements
-- statement:
--   Let $e:R\simeq S$ be a ring equivalence and let $r\in R$ be regular. Then $$e(r)\text{ is regular in }S.$$ This transports non-zero-divisor certificates across the explicit coordinate-ring equivalences.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

open Polynomial

theorem N25.isRegular_map_ringEquiv
    {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S)
    {r : R} (hr : IsRegular r) : IsRegular (e r) := by sorry
