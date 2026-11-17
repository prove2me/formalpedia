-- Prove2me | Theorems.Thm_N25_cuspArithmeticCensus_of_degree_bounds
-- name    : N25.cuspArithmeticCensus_of_degree_bounds
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:26.048615+00:00
-- url     : https://prove2.me/theorems/35088fef-d0f5-433b-a7ef-9379bfbce2b2
-- title:
--   Degree bounds determine the complete cusp census
-- statement:
--   Let $Q_4,Q_5$ be rational cusps of the level-$25$ curve with $\operatorname{ord}_{Q_4}(j_{25})=-5$ and $\operatorname{ord}_{Q_5}(j_{25})=-25$, and assume $\deg Q_4\ge4$ and $\deg Q_5\ge5$. Then there are exactly fourteen geometric cusps; the seven rational cusps can be enumerated with degree sequence $(1,1,1,1,1,4,5)$; moreover $\deg Q_4=4$, $\deg Q_5=5$, and every rational cusp is one of the five selected cusps or is $Q_4$ or $Q_5$:
--
--   $$\operatorname{Cusps}_{\mathbb Q}=\{p_0^{\mathbb Q},\ldots,p_4^{\mathbb Q},Q_4,Q_5\},\qquad(\deg Q_4,\deg Q_5)=(4,5).$$
--
--   This turns the two lower bounds into the exact closed-cusp decomposition.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option autoImplicit false
open AlgebraicCurve ModularCurve
open scoped MatrixGroups
open N25
open N25.Endgame

theorem N25.cuspArithmeticCensus_of_degree_bounds
    (Q₄ Q₅ : QPlace) (hc₄ : IsCusp j25 Q₄) (hc₅ : IsCusp j25 Q₅)
    (ho₄ : Q₄.ord j25 = -5) (ho₅ : Q₅.ord j25 = -25)
    (hd₄ : 4 ≤ Q₄.deg) (hd₅ : 5 ≤ Q₅.deg) :
    Nat.card {P : GPlace // IsCusp (emb25 j25) P} = 14 ∧
      (∃ e : Fin 7 ≃ {Q : QPlace // IsCusp j25 Q},
        ∀ i, (e i).1.deg = (![1,1,1,1,1,4,5] i : ℕ)) ∧
      Q₄.deg = 4 ∧ Q₅.deg = 5 ∧
      ∀ Q : QPlace, IsCusp j25 Q ↔
        (∃ i : Fin 5, Q = pQ25 i) ∨ Q = Q₄ ∨ Q = Q₅ := by sorry
