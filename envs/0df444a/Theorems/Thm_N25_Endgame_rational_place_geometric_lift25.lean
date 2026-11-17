-- Prove2me | Theorems.Thm_N25_Endgame_rational_place_geometric_lift25
-- name    : N25.Endgame.rational_place_geometric_lift25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:27.759601+00:00
-- url     : https://prove2.me/theorems/20a592f7-4df8-44f1-8c5e-3a4c1c3061ac
-- title:
--   Every rational place has a geometric place above it
-- statement:
--   Let $F_ℚ$ be the rational level-$25$ function field, let $F_{\overline{ℚ}}$ be its geometric constant extension, let $ι:F_ℚ→F_{\overline{ℚ}}$ be the coefficient embedding, and let $P$ be any place of $F_ℚ$. Then there exists a geometric place $W$ whose valuation ring contracts to that of $P$:
--
--   $$∃W∈Places(F_{\overline{ℚ}}),\quad 𝒪_W∩F_ℚ=𝒪_P.$$
--
--   This supplies the basic lying-over statement from which rational geometric lifts are refined.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension

set_option autoImplicit false
open ModularCurve AlgebraicCurve
open N25
open N25.Endgame

theorem N25.Endgame.rational_place_geometric_lift25 (P : QPlace) :
    ∃ W : GPlace, W.toValuationSubring.comap emb25.toRingHom = P.toValuationSubring := by sorry
