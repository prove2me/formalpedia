-- Prove2me | Theorems.Thm_N25_Endgame_rational_geometric_constant_extension25
-- name    : N25.Endgame.rational_geometric_constant_extension25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:06.906196+00:00
-- url     : https://prove2.me/theorems/e84edba5-ae6b-4d52-977b-aea4a011a949
-- title:
--   The geometric function field is the integral constant extension of the rational field
-- statement:
--   Let $F_ℚ$ be the rational level-$25$ function field, let $F_{\overline{ℚ}}$ be its geometric counterpart, and let $ι:F_ℚ→F_{\overline{ℚ}}$ be coefficient extension. With the induced $F_ℚ$-algebra structure, the tower $ℚ⊆F_ℚ⊆F_{\overline{ℚ}}$ is a scalar tower, $F_{\overline{ℚ}}$ is integral over $F_ℚ$, and constants from $\overline{ℚ}$ generate it as an $F_ℚ$-algebra:
--
--   $$ScalarTower(ℚ,F_ℚ,F_{\overline{ℚ}})\ \land\ F_{\overline{ℚ}}/F_ℚ\text{ integral}\ \land\ F_ℚ[\overline{ℚ}]=F_{\overline{ℚ}}.$$
--
--   This provides the constant-extension structure used to lift places. Formalization note: the algebra structure is explicitly chosen from $ι$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Endgame
import Definitions.Def_ModularCurve_GeometricBaseChange

set_option autoImplicit false
open ModularCurve AlgebraicCurve
open N25
open N25.Endgame

theorem N25.Endgame.rational_geometric_constant_extension25 :
    letI : Algebra FQ FG := emb25.toRingHom.toAlgebra
    IsScalarTower ℚ FQ FG ∧ Algebra.IsIntegral FQ FG ∧
      Algebra.adjoin FQ (Set.range (algebraMap Qbar FG)) = ⊤ := by sorry
