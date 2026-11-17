-- Prove2me | Theorems.Thm_N25_isLeftRegular_quotient_swap
-- name    : N25.isLeftRegular_quotient_swap
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:27.226524+00:00
-- url     : https://prove2.me/theorems/b21a8884-2514-4bf8-be9b-d8b69fd91913
-- title:
--   A regular sequence of length two may be swapped in a commutative ring
-- statement:
--   Let $B$ be a commutative ring and let $D,c\in B$. Assume multiplication by $D$ is injective on $B$, and multiplication by the class of $c$ is injective on $B/(D)$. Then multiplication by the class of $D$ is injective on $B/(c)$: $$D\text{ left-regular in }B,\ c\text{ left-regular in }B/(D)\ \Longrightarrow\ D\text{ left-regular in }B/(c).$$ This commutation lemma is used to change the order of quotient and localization regularity arguments.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

open Polynomial

theorem N25.isLeftRegular_quotient_swap
    {B : Type*} [CommRing B] {D c : B}
    (hD : IsLeftRegular D)
    (hc : IsLeftRegular
      (Ideal.Quotient.mk (Ideal.span ({D} : Set B)) c)) :
    IsLeftRegular
      (Ideal.Quotient.mk (Ideal.span ({c} : Set B)) D) := by sorry
