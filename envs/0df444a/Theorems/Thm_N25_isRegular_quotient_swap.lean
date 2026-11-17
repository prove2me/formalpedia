-- Prove2me | Theorems.Thm_N25_isRegular_quotient_swap
-- name    : N25.isRegular_quotient_swap
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:25.774201+00:00
-- url     : https://prove2.me/theorems/e6725f3f-4b6d-45fb-9095-b3c1f4326091
-- title:
--   Regularity survives swapping a two-element regular sequence
-- statement:
--   Let $B$ be a commutative ring and let $D,c\in B$. If $D$ is regular in $B$ and the class of $c$ is regular in $B/(D)$, then the class of $D$ is regular in $B/(c)$: $$D\text{ regular in }B,\ c\text{ regular in }B/(D)\ \Longrightarrow\ D\text{ regular in }B/(c).$$ This is the symmetric regular-sequence form needed for the canonical coordinate-ring construction.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

open Polynomial

theorem N25.isRegular_quotient_swap
    {B : Type*} [CommRing B] {D c : B}
    (hD : IsRegular D)
    (hc : IsRegular
      (Ideal.Quotient.mk (Ideal.span ({D} : Set B)) c)) :
    IsRegular
      (Ideal.Quotient.mk (Ideal.span ({c} : Set B)) D) := by sorry
