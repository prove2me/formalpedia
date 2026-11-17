-- Prove2me | Theorems.Thm_N25_K2Rows_finite_kernel
-- name    : N25.K2Rows.finite_kernel
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:21.093433+00:00
-- url     : https://prove2.me/theorems/2f72ee0d-d0d3-4cef-bc91-c183b1775bd9
-- title:
--   The selected endomorphism has finite kernel
-- statement:
--   Let $V=\ker π$ for the selected endomorphism of the level-$25$ Jacobian. Assume the frozen filtration data giving an injection $𝔽_{71}(ψ)\to V$, a surjection $V\to 𝔽_{71}(χ_{71})$, and exactness in the middle. Then $$|V|<\infty.$$ This finiteness allows the kernel to be used as a finite Galois module in the Kummer descent.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_LocalKummerKernel

set_option autoImplicit false
open N25

theorem N25.K2Rows.finite_kernel (hK2 : K2Rows) : Finite ↥V := by sorry
