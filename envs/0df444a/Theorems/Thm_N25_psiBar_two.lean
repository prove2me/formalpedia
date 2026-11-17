-- Prove2me | Theorems.Thm_N25_psiBar_two
-- name    : N25.psiBar_two
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:45:09.552831+00:00
-- url     : https://prove2.me/theorems/2d34da8a-ca3f-473a-bae3-10ef062ae9c0
-- title:
--   The residue character sends $2$ to $57$ modulo $71$
-- statement:
--   For the explicit character $ψ̄:(ℤ/25ℤ)^×→(ℤ/71ℤ)^×$, $$ψ̄(2)=57\pmod{71}.$$ This fixes a generator value for the order-five character used in the local and global descent.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_LocalKummerCharacter
import Definitions.Def_N25

open N25

theorem N25.psiBar_two : psiBar (ZMod.unitOfCoprime 2 (by decide)) =
    ZMod.unitOfCoprime 57 (by decide) := by sorry
