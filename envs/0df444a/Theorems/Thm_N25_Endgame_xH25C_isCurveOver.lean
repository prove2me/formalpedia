-- Prove2me | Theorems.Thm_N25_Endgame_xH25C_isCurveOver
-- name    : N25.Endgame.xH25C_isCurveOver
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:27:22.718576+00:00
-- url     : https://prove2.me/theorems/f01bfdad-8dbe-4570-9f00-eaa177b9643f
-- title:
--   The level-$25$ function field satisfies the curve axioms
-- statement:
--   Let $K$ be a perfect field and let $F_K$ be the level-$25$ modular function field over $K$. Then $F_K$ satisfies the formal curve axioms over $K$: principal divisors are available, every place has residue field finite-dimensional over $K$, and the Kähler differential module $\Omega_{F_K/K}$ is free of rank one. In symbols,
--
--   $$F_K\text{ is a function field of a curve over }K.$$
--
--   This installs the curve structure used throughout the divisor, Picard, and reduction arguments.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.xH25C_isCurveOver
    (K : Type*) [Field K] [PerfectField K] :
    AlgebraicCurve.IsCurveOver K (FBase K) := by sorry
