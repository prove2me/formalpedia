-- Prove2me | Theorems.Thm_N25_cusp_pole_lift_bijection
-- name    : N25.cusp_pole_lift_bijection
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:16.861538+00:00
-- url     : https://prove2.me/theorems/ece99785-e761-4ad5-91db-b061736dcd9f
-- title:
--   Geometric poles lift bijectively to complex poles
-- statement:
--   Fix an embedding $\iota:\overline{\mathbb Q}\hookrightarrow\mathbb C$. Let $F$ be the geometric level-$25$ function field and $F_{\mathbb C}$ its complex base change. There exist a coefficientwise map $\kappa:F\to F_{\mathbb C}$ and elements $j\in F$, $j_{\mathbb C}\in F_{\mathbb C}$ with the standard $j$-series and $\kappa(j)=j_{\mathbb C}$ such that both pole sets are finite of cardinality fourteen and there is an equivalence
--
--   $$\{P:\operatorname{ord}_P(j)<0\}\simeq\{P':\operatorname{ord}_{P'}(j_{\mathbb C})<0\}$$
--
--    preserving contraction and the order of every function. This transports the complex cusp census back to the geometric field.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
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

set_option autoImplicit false
open ModularCurve AlgebraicCurve
open N25

theorem N25.cusp_pole_lift_bijection
    (ι : AlgebraicClosure ℚ →+* ℂ) :
    let K := AlgebraicClosure ℚ
    let F₀ := xHFunctionField 25 N25.H25
    let F := xHFunctionFieldBar 25 N25.H25
    let Fℂ := laurentBaseChange ℂ F₀
    ∃ κ : F →+* Fℂ, ∃ j : F, ∃ jℂ : Fℂ,
      (∀ x : F, (κ x : LaurentSeries ℂ) = coeffMap ι (x : LaurentSeries K)) ∧
      (j : LaurentSeries K) = jqModC K ∧
      (jℂ : LaurentSeries ℂ) = jqModC ℂ ∧ κ j = jℂ ∧
      Finite {P : Place K F // P.ord j < 0} ∧
      Finite {P : Place ℂ Fℂ // P.ord jℂ < 0} ∧
      Nat.card {P : Place K F // P.ord j < 0} = 14 ∧
      Nat.card {P : Place ℂ Fℂ // P.ord jℂ < 0} = 14 ∧
      ∃ lift : {P : Place K F // P.ord j < 0} ≃
          {P : Place ℂ Fℂ // P.ord jℂ < 0},
        ∀ P, (lift P).val.toValuationSubring.comap κ = P.val.toValuationSubring ∧
          ∀ x : F, (lift P).val.ord (κ x) = P.val.ord x := by sorry
