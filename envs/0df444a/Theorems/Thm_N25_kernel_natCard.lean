-- Prove2me | Theorems.Thm_N25_kernel_natCard
-- name    : N25.kernel_natCard
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:44:01.785921+00:00
-- url     : https://prove2.me/theorems/b3d2b9fc-f679-434f-bc24-c2c03f2e452e
-- title:
--   The selected endomorphism has kernel of order $71^2$
-- statement:
--   Let $J$ be the geometric Jacobian carrier, let $γ$ be the order-five diamond operator, and let $π=2+4γ+γ^2$. Assume the cyclotomic relation $1+γ+γ^2+γ^3+γ^4=0$ on $J$, and write $V=ker(π)$. Then $$|V|=71^2.$$ This identifies the finite Galois module on which the Kummer descent is carried out.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_LocalKummerPolynomial

set_option autoImplicit false
open N25

theorem N25.kernel_natCard (hPhi : PhiFiveZero) : Nat.card ↥V = 71 ^ 2 := by sorry
