-- Prove2me | Theorems.Thm_N25_psiBar_ker
-- name    : N25.psiBar_ker
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:45:25.449997+00:00
-- url     : https://prove2.me/theorems/2cec57bd-75b0-4a5a-b79b-7be14c384f1c
-- title:
--   The kernel of the residue character is exactly $H_{25}$
-- statement:
--   Let $ψ̄:(ℤ/25ℤ)^×→(ℤ/71ℤ)^×$ be the explicit order-five residue character and let $H_{25}=⟨7⟩$. Then $$ker(ψ̄)=H_{25}.$$ This identifies the character field and the twisted line in the kernel filtration.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_LocalKummerCharacter
import Definitions.Def_N25

open N25

theorem N25.psiBar_ker : psiBar.ker = H25 := by sorry
