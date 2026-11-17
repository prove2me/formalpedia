-- Prove2me | Theorems.Thm_N25_Endgame_SpecialUnitPoleDegrees_finrank_eq_sum_poles
-- name    : N25.Endgame.SpecialUnitPoleDegrees.finrank_eq_sum_poles
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:19.645237+00:00
-- url     : https://prove2.me/theorems/ca14157c-69a4-474d-be0b-a9391d4a61a8
-- title:
--   The degree of a simple function-field extension equals total pole degree
-- statement:
--   Let $p$ be prime with $p=2$ or $p=3$, let $R$ be a reduction datum, write $κ=κ(R.A)$ and $F=F_{special}(R.A)$, and let $Q_i$ for $i∈Fin(5)$ be the five reduced selected cusps. Assume $F/κ$ has the stated curve structure, $L_F(0)$ is finite-dimensional over $κ$, $f∈F$ is transcendental, and $F/κ(f)$ is finite-dimensional. Let integers $a_i$ satisfy $ord_{Q_i}(f)=a_i$, and assume $ord_P(f)=0$ at every place $P$ distinct from all $Q_i$. Then
--
--   $$[F:κ(f)]=∑_{i∈Fin(5)}max(0,-a_i).$$
--
--   This computes simple-extension degree directly from the complete list of poles.
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

theorem N25.Endgame.SpecialUnitPoleDegrees.finrank_eq_sum_poles
    [IsCurveOver (κ R.A) (FSpecial R.A)] [FiniteDimensional (κ R.A) (LSpace (0 : Divisor (κ R.A) (FSpecial R.A)))]
    (f : (FSpecial R.A)) (hf : Transcendental (κ R.A) f)
    [FiniteDimensional (IntermediateField.adjoin (κ R.A) ({f} : Set (FSpecial R.A))) (FSpecial R.A)]
    (a : Fin 5 → ℤ) (ha : ∀ i, (redPlace25 R (pG25 i)).ord f = a i)
    (hs : ∀ P : (SpecialPlace R.A), (∀ i, P ≠ redPlace25 R (pG25 i)) → P.ord f = 0) :
    (Module.finrank (IntermediateField.adjoin (κ R.A) ({f} : Set (FSpecial R.A))) (FSpecial R.A) : ℤ) =
      ∑ i : Fin 5, max 0 (-a i) := by sorry
