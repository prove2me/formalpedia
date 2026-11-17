-- Prove2me | Theorems.Thm_N25_Endgame_SpecialUnitPoleDegrees_special_simple_finiteDimensional25
-- name    : N25.Endgame.SpecialUnitPoleDegrees.special_simple_finiteDimensional25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:33.507609+00:00
-- url     : https://prove2.me/theorems/53e2ed3b-8927-4858-96fa-b1edd212512e
-- title:
--   A transcendental function gives a finite simple subextension
-- statement:
--   Let $p$ be prime, let $R$ be a level-$25$ reduction datum at $p$, write $κ=κ(R.A)$ and $F=F_{special}(R.A)$, and let $f∈F$ be transcendental over $κ$. Then $F$ is finite-dimensional over the simple intermediate field $κ(f)$:
--
--   $$[F:κ(f)]<∞.$$
--
--   This supplies the finiteness hypothesis needed to identify simple-extension degree with total pole degree.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Units
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_UnitOrders
import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType

set_option autoImplicit false
open AlgebraicCurve N25.Endgame
open N25
open N25.Endgame
open N25
variable {p : ℕ} [Fact p.Prime] (hp : p = 2 ∨ p = 3) (R : RedDatum25 p)
include hp
omit hp

theorem N25.Endgame.SpecialUnitPoleDegrees.special_simple_finiteDimensional25
    (f : FSpecial R.A) (hf : Transcendental (κ R.A) f) :
    FiniteDimensional (IntermediateField.adjoin (κ R.A) ({f} : Set (FSpecial R.A)))
      (FSpecial R.A) := by sorry
