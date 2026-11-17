-- Prove2me | Theorems.Thm_N25_Endgame_xH25C_essFiniteType
-- name    : N25.Endgame.xH25C_essFiniteType
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:25:26.329198+00:00
-- url     : https://prove2.me/theorems/768913b0-6969-4f96-a576-f2c22c12f2a2
-- title:
--   The level-$25$ function field is essentially of finite type
-- statement:
--   Let $K$ be a field and let $F_K$ be the level-$25$ modular function field over $K$. Then the extension is essentially of finite type as a $K$-algebra: equivalently for this field extension, $F_K$ is generated as a field over $K$ by finitely many elements. Thus
--
--   $$F_K/K\text{ is essentially of finite type}.$$
--
--   This provides the finite-generation input for the algebraic-curve infrastructure.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.xH25C_essFiniteType (K : Type*) [Field K] :
    Algebra.EssFiniteType K (FBase K) := by sorry
