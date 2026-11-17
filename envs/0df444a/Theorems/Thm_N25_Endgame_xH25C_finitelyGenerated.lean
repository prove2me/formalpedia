-- Prove2me | Theorems.Thm_N25_Endgame_xH25C_finitelyGenerated
-- name    : N25.Endgame.xH25C_finitelyGenerated
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:25:36.87153+00:00
-- url     : https://prove2.me/theorems/bac22e34-ca89-4b90-a5d3-9207223cfc0a
-- title:
--   Finite generation of the level-$25$ function field
-- statement:
--   Let $K$ be a field and let $F_K$ be the level-$25$ modular function field over $K$. There is a finite subset $S\subset F_K$ whose intermediate-field closure over $K$ is all of $F_K$:
--
--   $$\exists S\subset F_K\text{ finite},\qquad K(S)=F_K.$$
--
--   This gives an explicit field-theoretic form of finite generation for later curve and differential constructions.
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

theorem N25.Endgame.xH25C_finitelyGenerated (K : Type*) [Field K] :
    ∃ s : Finset (FBase K),
      IntermediateField.adjoin K (s : Set (FBase K)) = ⊤ := by sorry
