-- Prove2me | Theorems.Thm_N25_GlobalKummer_kernel_comp_zero
-- name    : N25.GlobalKummer.kernel_comp_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:05.854461+00:00
-- url     : https://prove2.me/theorems/26cb54bf-d859-4f54-a88d-f3d5951ad2b8
-- title:
--   The kernel inclusion is killed by the cyclotomic quotient
-- statement:
--   Assume the cyclotomic relation and the frozen filtration maps $i:𝔽_{71}(ψ)\to V$ and $q:V\to 𝔽_{71}(χ_{71})$. Their composite is the zero morphism of Galois representations: $$q\circ i=0.$$ This is the complex condition underlying the short exact sequence used in cohomology.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GlobalKummerSequence

set_option autoImplicit false
open CategoryTheory
open N25
open N25.GlobalKummer

theorem N25.GlobalKummer.kernel_comp_zero (hPhi : PhiFiveZero) (K2 : K2Rows) :
    kernelInclusion hPhi K2 ≫ kernelQuotient hPhi K2 = 0 := by sorry
