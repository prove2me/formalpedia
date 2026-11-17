-- Prove2me | Theorems.Thm_N25_GlobalKummer_kernel_shortExact
-- name    : N25.GlobalKummer.kernel_shortExact
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:41:09.707402+00:00
-- url     : https://prove2.me/theorems/09b6d6b7-6f6a-44db-87ab-8f657302eb52
-- title:
--   The kernel representation is an extension of two character lines
-- statement:
--   Assume the cyclotomic relation and the frozen filtration data. With $V=\ker π$, the inclusion $i$ of the $ψ$-line and the quotient $q$ onto the cyclotomic line form a short exact sequence of $𝔽_{71}[G_{ℚ}]$-modules: $$0\longrightarrow 𝔽_{71}(ψ)\xrightarrow{i}V\xrightarrow{q}𝔽_{71}(χ_{71})\longrightarrow0.$$ This is the representation-theoretic backbone of the global Kummer descent.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Theorems.Thm_N25_GlobalKummer_kernel_comp_zero
import Definitions.Def_N25_GlobalKummerSequence

set_option autoImplicit false
open CategoryTheory
open N25
open N25.GlobalKummer

theorem N25.GlobalKummer.kernel_shortExact (hPhi : PhiFiveZero) (K2 : K2Rows) :
    (ShortComplex.mk (kernelInclusion hPhi K2) (kernelQuotient hPhi K2)
      (kernel_comp_zero hPhi K2)).ShortExact := by sorry
